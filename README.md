# Formalización en Lean

Este repositorio forma parte del Trabajo de fin de Máster *Fundamentos del demostrador Lean* de Rodrigo Pallares Palencia. Más concretamente, la carpeta `Scripts` contiene los ficheros correspondientes al capítulo 3 del trabajo. Los ficheros están escritos en Lean 4. 

En este repositorio no se pretende llevar a cabo formalizaciones novedosas ni pruebas complicadas, sino mostrar de forma didáctica cómo puede ponerse en marcha la maquinaria de tipos de Lean para formalizar matemáticas. De hecho, muchas de las definiciones que aparecen en este repositorio están inspiradas en formalizaciones de la librería [mathlib](https://github.com/leanprover-community/mathlib).

Los ficheros del repositorio son los siguientes:
- `logic.lean`: se prueban aquí todos los resultados sobre lógica proposicional que se han necesitado para el resto de definiciones y teoremas del repositorio.
- `set_theory.lean`: en este fichero se definen nociones básicas sobre Teoría de Conjuntos y se prueban propiedades sobre ellas. Algunas de las nociones tratadas son: 
    - El tipo de los conjuntos de elementos de un tipo
    - El conjunto vacío
    - El conjunto total
    - Unión e intersección finita y arbitraria de conjuntos
    - Conjuntos unitarios
    - Conjuntos complementarios
    - Conjuntos disjuntos
    - Imagen e imagen inversa de un conjunto por una función
- `finite.lean`: en este fichero se define la noción de conjunto finito y se prueban propiedades sobre conjuntos finitos. También se da una definición alternativa de conjunto finito y se prueba que ambas definiciones son equivalentes.
- `topology.lean`: en este fichero se define el tipo de los espacios topológicos sobre un tipo y se prueba que un espacio topológico viene determinado por la noción de abierto asociada. También se define un término que permite dotar de topología a un tipo describiendo sus cerrados en lugar de sus abiertos.
- `topology_defs.lean`: en este fichero se definen nociones sobre Topología y se prueban resultados al respecto. Algunas de las nociones tratadas son:
    - El interior de un conjunto
    - Sucesiones convergentes
    - Funciones continuas
    - Topología generada por una subbase
    - Compacidad por recubrimientos 
    - Espacios de Hausdorff
    - Topología compacto-abierta
