## Correcciones

### En cuanto a syntax sugar y elaboración:

1. [x]    Les faltó hacer la eta-expansión del operador print. Esto sirve para obtener una "aplicación parcial" de print. Fijense que está explicado en el punto 1.3 del apunte de azúcar sintáctico. Por ejemplo, el siguiente programa debería ser válido: let f (g: Nat -> Nat) = g 10 in f (print "res=")
2. [x]    Revisen la elaboración de términos recursivos (énfasis en términos, no declaraciones). Por ejemplo, el test 230-inner_rec.fd4 no pasa. También pueden probar desde el intérprete con un ejemplo más simple que debería ser válido pero no compila: let rec f (x:Nat) :Nat = ifz x then x else (1 + f (x-1)) in f 10

### En cuanto a Bytecode:

3. []    En la Macchina (la máquina virtual escrita en C) está mal el orden de los prints. Pueden correr el test 310-orden_print.fd4para verificar cuando lo corrijan.
4. []    En la ejecución en la máquina implementada en Haskell fallan los tests. Pueden usar 100-letfun.fd4 como ejemplo. El
    mensaje de error que obtienen va a servirles para empezar a ver qué operación revisar.

### Optimizaciones:

5. []    Está buena la idea de agregar todos los prints indicando qué optimización se aplicó en cada paso, pero debería estar
    escondida detrás de una opción de _debugging_. Esto también les va a permitir poder correr los tests de "EVALOPT". De
    todas formas, no hace falta que implementen la opción de _debugging_, solo se los menciono a modo feedback. Pueden
    comentar los printFD4 para correr los tests.

6. []    Las optimizaciones obligatorias (_constant folding & propagation_) están bien. La optimización opcional que
    implementaron, _common subexpression elimination_, introduce un error de tipos en _runtime_. Revisar. Pueden usar
    el test 405-common_subexpression.fd4 como referencia.

### Profiling:

7. []    Faltó implementar profiling. Está en el apunte junto a optimizaciones. Si no lo tienen se los puedo pasar.

### Conversión de clausura:

8. []    No logro que me pasen los tests. Por ejemplo, el test 110-letfun2.fd4 , falla con los siguientes errores:
