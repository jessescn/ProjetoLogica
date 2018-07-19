module PetShop
abstract sig Animal {
    brinde: one Brinde
}

abstract sig Brinde{}

sig gaiola, racao extends Brinde{}

sig AnimalPequeno, AnimalMedio, AnimalGrande extends Animal{}

sig Pessoa {
    adocoes: set Animal
}

fact Nome {
    all p: Pessoa | some animaisDasAdocoes[p]
    all a: Animal | lone dono[a]
    all b: Brinde | umBrinde[b]
    all p : Pessoa | tresAnimais[p]
    all a: Animal | (isAnimalMedio[a] || isAnimalPequeno[a]) => brindeDoAnimal[a] in gaiola
    all a: Animal | (a in AnimalGrande) => brindeDoAnimal[a] in racao
    all p: Pessoa | (#animaisDasAdocoes[p] >= 1) =>  (some a: animaisDasAdocoes[p] | isAnimalPequeno[a])
}

fun brindeDoAnimal[a: Animal]: set Brinde{
    a.brinde
}

fun animaisDasAdocoes[p:Pessoa]: set Animal {
    p.adocoes
}

fun dono[a: Animal]: set Pessoa {
    a.~adocoes
}

pred isAnimalMedio[a: Animal]{
   a in AnimalMedio
}

pred isAnimalPequeno[a: Animal]{
    a in AnimalPequeno
}

pred isAnimalGrande[a: Animal]{
    a in AnimalGrande
}

pred umBrinde[b: Brinde]{
    one brinde.b
}

pred tresAnimais[p: Pessoa]{
    #p.adocoes <= 3
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
assert NenhumAnimalPequenoComRacao{
	all a : Animal | (isAnimalPequeno[a]) => not a.brinde in racao
}

--- nenhum animal grande pode ter gaiola
assert NenhumAnimalGrandeComGaiola{
	all a : Animal | (isAnimalGrande[a]) => not a.brinde in gaiola
}

--- nenhum animal pode ter mais de um dono
assert AnimalComMaisDeUmDono{
	all a: Animal | not  #dono[a] > 1
}

--- nenhuma pessoa pode ter 0 animais
assert PessoaSemAnimal{
	all p: Pessoa | not #animaisDasAdocoes[p] = 0
}

check PessoaSemAnimal
check max3PorPessoa
check peloMenosUmAnimalPequeno
check NenhumAnimalPequenoComRacao
check NenhumAnimalGrandeComGaiola
check AnimalComMaisDeUmDono


