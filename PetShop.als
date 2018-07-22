module PetShop

// Objeto que representa um animal, que possui um acessorio
abstract sig Animal {
    acessorio: one Acessorio
}

// Animal pode ser do tipo Pequeno, Médio e Grande
sig AnimalPequeno, AnimalMedio, AnimalGrande extends Animal{}

// Objeto que representa o acessorio que acompanha cada animal
abstract sig Acessorio{}

// Os acessorios podem ser do tanto uma gaiola(Para os tipos Pequeno e Médio) quanto uma
// racao (para os do tipo Grande)
sig gaiola, racao extends Acessorio{}

// Objeto que representa uma pessoa que adotou algum animal 
sig Pessoa {
    adocoes: set Animal
}

-- Fatos --

fact Premissas {
    
    all p: Pessoa | some animaisDasAdocoes[p]
    all a: Animal | lone dono[a]
    all ac: Acessorio | umAcessorio[ac]
    all p: Pessoa | tresAnimais[p]
    all a: Animal | (isAnimalMedio[a] || isAnimalPequeno[a]) => acessorioDoAnimal[a] in gaiola
    all a: Animal | (a in AnimalGrande) => acessorioDoAnimal[a] in racao
    all p: Pessoa | (#animaisDasAdocoes[p] >= 1) =>  (some a: animaisDasAdocoes[p] | isAnimalPequeno[a])
    all p: Pessoa | (#animaisDasAdocoes[p]  = 3) => not todosPequenos[p]
    all p: Pessoa |  not umDeCada[p]
    all p: Pessoa | apenasUmGrande[p]

}

-- Funcoes --

// Retorna o respectivo acessorio do animal
fun acessorioDoAnimal[a: Animal]: set Acessorio{
    a.acessorio
}

// Retorna os animais adotados de uma pessoa
fun animaisDasAdocoes[p:Pessoa]: set Animal {
    p.adocoes
}

// Retorna o respectivo dono do animal
fun dono[a: Animal]: set Pessoa {
    a.~adocoes
}

-- Predicados --

// Pode haver apenas um animal grande por adocao
pred apenasUmGrande[p: Pessoa]{

  lone g : AnimalGrande | g in p.adocoes
}

// NEG : Em uma adocao, todos os animais sao pequenos
pred todosPequenos[p:Pessoa]{
    all a : p.adocoes | a in AnimalPequeno 
}

// NEG: Existe uma adocao onde se encontram todos os tipos
pred umDeCada[p:Pessoa]{
      (#animaisDasAdocoes[p] = 3) => some a : animaisDasAdocoes[p] | a in AnimalPequeno && some a : animaisDasAdocoes[p] | a in AnimalMedio &&  some a : animaisDasAdocoes[p]| a in AnimalGrande	
}

// Retorna o acessorio do animal
pred umAcessorio[ac: Acessorio]{
    one acessorio.ac
}

// A quantidade maxima de animais por adocao é 3
pred tresAnimais[p:Pessoa]{
    #p.adocoes <= 3
}

// Retorna true se o animal é do tipo pequeno, e false caso não seja
pred isAnimalPequeno[a: Animal]{
    a in AnimalPequeno
}

// Retorna true se o animal é do tipo medio, e false caso não seja
pred isAnimalMedio[a: Animal]{
   a in AnimalMedio
}

// Retorna true se o animal é do tipo grande, e false caso não seja
pred isAnimalGrande[a: Animal]{
    a in AnimalGrande
}



--------------------------TESTES-------------------------------

--- não pode ter pessoa com mais de 3 animais
assert max3PorPessoa{
	all p: Pessoa | #animaisDasAdocoes[p] <= 3
}

--- não pode ter adoção sem nenhum animal pequeno
assert peloMenosUmAnimalPequeno{
	 all p: Pessoa | (#animaisDasAdocoes[p] >= 1) =>  (some a: animaisDasAdocoes[p] | isAnimalPequeno[a])
}

--- nenhum animal pequeno pode ter ração
assert nenhumAnimalPequenoComRacao{
	all a: Animal | (isAnimalPequeno[a]) => not a.acessorio in racao
}

--- nenhum animal grande pode ter gaiola
assert nenhumAnimalGrandeComGaiola{
	all a: Animal | (isAnimalGrande[a]) => not a.acessorio in gaiola
}

--- nenhum animal pode ter mais de um dono
assert animalComMaisDeUmDono{
	all a: Animal | not  #dono[a] > 1
}

--- nenhuma pessoa pode ter 0 animais
assert pessoaSemAnimal{
	all p: Pessoa | not #animaisDasAdocoes[p] = 0
}
-- nenhuma doacao com todos sendo animais pequenos
assert todosPequenos{
	all p: Pessoa | not todosPequenos[p]
}

--- Todos os testes juntos (Obs. o Alloy so roda o primeiro teste)  
assert All{

     all p: Pessoa | not todosPequenos[p]
	all p: Pessoa | not #animaisDasAdocoes[p] = 0
     all a: Animal | not  #dono[a] > 1
     	all a: Animal | (isAnimalGrande[a]) => not a.acessorio in gaiola
	all a: Animal | (isAnimalPequeno[a]) => not a.acessorio in racao
	all p: Pessoa | (#animaisDasAdocoes[p] >= 1) =>  (some a: animaisDasAdocoes[p] | isAnimalPequeno[a])
	all p: Pessoa | #animaisDasAdocoes[p] <= 3
     all p: Pessoa | apenasUmGrande[p]
}


-- Checks e Runs --

pred show[]{
}
run show

check All
check todosPequenos
check pessoaSemAnimal
check max3PorPessoa
check peloMenosUmAnimalPequeno
check nenhumAnimalPequenoComRacao
check nenhumAnimalGrandeComGaiola
check animalComMaisDeUmDono


