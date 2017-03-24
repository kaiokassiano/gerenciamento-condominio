module projeto
open util/ordering[Time]

-- Assinaturas
sig Time {}

sig Empresa {
	condominios: Condominio -> Time
}

sig Condominio {
	casas: Casa -> Time
}

sig Casa {
	caixaDaCasa: one CaixaDAgua,
	moradorCasa: Morador -> Time
}

sig CaixaDAgua {
	estadoCaixa: EstadoCaixa -> Time
}

abstract sig EstadoCaixa {}

sig Cheia extends EstadoCaixa {}

sig Vazia extends EstadoCaixa {}

sig Morador {
	estadoMorador: EstadoMorador -> Time
}

abstract sig EstadoMorador {}

sig EmDebito extends EstadoMorador {}

sig EmDia extends EstadoMorador {}

-- Funções auxiliares --

-- Retorna o morador de uma casa dado um tempo
fun moradorCasa[casa: Casa, t: Time] : Morador {
	casa.moradorCasa.t
}

-- Retorna o estado do morador dado um tempo
fun getEstadoMorador[m: Morador, t: Time] : EstadoMorador {
	m.estadoMorador.t
}

-- Retorna os condomínios da empresa dado um tempo
fun condominios[e: Empresa, t: Time] : Condominio {
	e.condominios.t
}

-- Retorna as casas de um condomínio dado um tempo
fun casas[condominio: Condominio, t: Time] : Casa {
	condominio.casas.t
}

-- Retorna as casas a qual dada caixa de água pertence
fun casa[caixa: CaixaDAgua] : Casa {
	caixa.~caixaDaCasa
}

-- Retorna o estado da caixa de água dado um tempo
fun estadoCaixa [caixa: CaixaDAgua, t: Time] : EstadoCaixa {
	caixa.estadoCaixa.t
}

-- Predicados e Fatos --
-- Regras Empresa --

-- Toda empresa tem algum condomínio mas no máximo 2
pred limitesCondominiosEmpresa[t: Time] {
	#condominios[Empresa, t] > 0 and #condominios[Empresa, t] <= 2
}

fact empresaFatos {
	all t: Time | limitesCondominiosEmpresa[t]
	one Empresa
}

-- Regras condominio --

-- Condominio tem até 10 casas e no mínimo 5 para um dado tempo
pred limiteCasasCondominio[condominio: Condominio, t: Time] {
	#casas[condominio, t] <= 10 and	#casas[condominio, t] > 4
}

-- Condomínio pertence a uma empresa
pred condominioPertenceAUmaEmpresa[condominio: Condominio, t: Time] {
	one condominios[Empresa, t] & condominio
}

fact condominioFatos {
	all condominio: Condominio, t: Time | limiteCasasCondominio[condominio, t]
		 and condominioPertenceAUmaEmpresa[condominio, t]
}

-- Regras morador --

-- Todo morador tem uma, e apenas uma casa
pred umaCasaPorMorador[morador: Morador, t: Time] {
	one moradorCasa.t.morador
}

fact moradorFatos {
	all morador: Morador, t: Time | umaCasaPorMorador[morador, t]
		and one getEstadoMorador[morador, t]  -- Morador tem apenas um estado por tempo

	one EmDebito  -- Singleton
	one EmDia -- Singleton
}

-- Regras casa -- 

-- Casa pertence a apenas um condomínio
pred casaPertenceUmCondominio[casa: Casa, t: Time] {
	one casa.~(casas.t)
}

fact casaFatos {
	all casa: Casa, t: Time | casaPertenceUmCondominio[casa, t]
		and lone moradorCasa[casa, t] -- Toda casa tem zero ou um morador
}

-- Regras caixa --

fact caixaFatos {
	Casa.caixaDaCasa & CaixaDAgua = CaixaDAgua -- Não há caixas soltas

	all caixa: CaixaDAgua, t: Time | one casa[caixa] -- Cada caixa pertence apenas a uma casa
		and one estadoCaixa[caixa, t] -- Caixa tem sempre só um estado
	
	one Cheia -- Singleton
	one Vazia -- Singleton
}

-- Predicados de mudança de estado com tempo
pred mudarEstadoCaixa[caixa: CaixaDAgua, estado: EstadoCaixa, t1, t2: Time] {
	estado != estadoCaixa[caixa, t1]
	estadoCaixa[caixa, t2] = estado
}


pred mudancaDeMorador[casa: Casa, morador: Morador, t1, t2: Time] {
	morador != moradorCasa[casa, t1]
	moradorCasa[casa, t2] = morador 
}

pred saidaDeMorador[casa: Casa, morador: Morador, t1, t2: Time] {
	morador = moradorCasa[casa, t1]
	no moradorCasa[casa, t2]
}

pred chegadaDeMorador[casa: Casa, morador: Morador, t1, t2: Time] {
	no moradorCasa[casa, t1]
	moradorCasa[casa, t2] = morador
}

pred mudarEstadoMorador[morador: Morador, estadoMorador: EstadoMorador, t1, t2: Time] {
	estadoMorador != getEstadoMorador[morador, t1]
	getEstadoMorador[morador, t2] = estadoMorador
}

-- Asserts

assert naoCondominioMenosCincoCasas {
	all cond: Condominio, t: Time | #cond.casas.t > 4
}

assert naoCasaMaisDeUmMorador {
	all casa: Casa, t: Time | #casa.moradorCasa.t < 2
}

assert naoEmpresaMaisDeDoisCondominios {
	all empresa: Empresa, t: Time | #empresa.condominios.t < 3
}

assert todoMoradorPertenceApenasUmaCasa {
	all morador: Morador, t: Time | #((moradorCasa.t).morador) < 2
} 

-- check naoCondominioMenosCincoCasas for 10
-- check naoCasaMaisDeUmMorador for 10
-- check naoEmpresaMaisDeDoisCondominios for 10
-- check todoMoradorPertenceApenasUmaCasa for 10


-- "main"
pred init[t: Time] {
}

fact traces{
    init[first]
		all pre: Time-last | let pos = pre.next |
		some estado: EstadoCaixa, caixa: CaixaDAgua, casa : Casa, morador : Morador, estadoMorador: EstadoMorador|
		mudancaDeMorador[casa, morador, pre, pos] or saidaDeMorador[casa, morador, pre, pos] or chegadaDeMorador[casa, morador, pre, pos]
		or mudarEstadoCaixa[caixa, estado, pre, pos]
		or mudarEstadoMorador[morador, estadoMorador, pre, pos]
}

pred show[] {
	#Condominio = 2
	#Morador  = 6
	#Casa = 11
}	

run show for 11


