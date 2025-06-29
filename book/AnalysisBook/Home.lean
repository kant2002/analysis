import VersoBlog
open Verso Genre Blog

#doc (Page) " Часткова формалізація в Lean книги Аналіз I" =>

Файли в цьому каталозі містять формалізацію вибраних частин мого *(пр.перекл. тут і далі це Терренс Тао)* тексту [_Аналіз I_](https://terrytao.wordpress.com/books/analysis-i/) у [Lean](https://lean-lang.org/). Формалізація має на меті максимально точно перефразувати оригінальний текст, а також продемонструвати особливості та синтаксис Lean. Зокрема, формалізація _не_ оптимізована під ефективність, а в деяких випадках може відхилятися від ідіоматичного використання Lean.

Частини тексту, залишені як вправи для читача, у цьому перекладі передаються як тактика `sorry`. Читачі можуть створити форк репозиторію, щоб спробувати свої сили у виконанні цих вправ, але я не маю наміру розміщувати рішення безпосередньо в цьому репозиторії.

Хоча розташування визначень, теорем і доказів тут є близьким перефразуванням підручника, я утримуюся від прямого цитування матеріалу з підручника, натомість наводжу посилання на оригінальний текст, де це доречно. Таким чином, цю формалізацію слід розглядати як анотоване доповнення до основного тексту, а не як його заміну.

Значна частина матеріалу в цьому тексті продубльована у стандартній математичній бібліотеці Lean [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), хоча й з дещо іншими визначеннями. Щоб усунути ці розбіжності, ця формалізація поступово переходитиме від визначень, наданих підручником, до визначень, наданих Mathlib, у міру просування в тексті, жертвуючи таким чином самодостатністю формалізації на користь сумісності з Mathlib. Наприклад, у розділі 2 розвивається теорія натуральних чисел незалежно від Mathlib, але в усіх наступних розділах замість неї використовуватимуть натуральні числа Mathlib. (Епілог до розділу 2 надається, щоб показати, що два поняття натуральних чисел ізоморфні.) Таким чином, цю формалізація також може бути використана як вступ до різних частин Mathlib.

Для узгодження формалізації з домовленостями Mathlib, до деяких визначень було внесено невелику кількість технічних змін порівняно з версією підручника. Найбільш помітні:
- Послідовності індексуються з нуля, а не з одиниці, оскільки Mathlib має набагато більше підтримки для натуральних чисел `ℕ` з нульовою нумерацією, ніж для натуральних чисел з одиничною нумерацією.
- Багатьом операціям, які залишилися невизначеними в тексті, таким як ділення на нуль або отримання формальної границі не-Коші послідовності, замість цього присвоюється "сміттєве" значення (наприклад, `0`), щоб зробити операцію повністю визначеною. Це пояснюється тим, що Lean має кращу підтримку повних функцій *(пр.перекл. total functions)*, ніж часткових функцій *(пр.перекл. partial functions)* (нерозбірливе використання останніх може призвести до "пекла залежних типів", в якому навіть дуже прості маніпуляції вимагають досить тонких і делікатних доказів). Дивіться, наприклад, [цю публікацію в блозі](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/) Кевіна Баззарда для отримання додаткової інформації.

Поточні формалізовані розділи:

- [Section 2.1: Аксіоми Пеано](./sec21/)
- [Section 2.2: Додавання](./sec22/)
- [Section 2.3: Множення](./sec23/)
- [Chapter 2, епілог: Ізоморфізм із натуральними числами Mathlib](./sec2e)
- [Section 3.1: Set theory fundamentals](./sec31/)
- [Section 3.2: Russel's paradox](./sec32/)
- [Section 3.3: Functions](./sec33/)
- [Section 3.4: Images and inverse images](./sec34/)
- [Section 3.5: Cartesian products](./sec35/)
- [Section 3.6: Cardinality of sets](./sec36/)
- [Section 4.1: The integers](./sec41/)
- [Section 4.2: The rationals](./sec42/)
- [Section 4.3: Absolute value and exponentiation](./sec43/)
- [Section 4.4: Gaps in the rational numbers](./sec44/)
- [Section 5.1: Cauchy sequences of rationals](./sec51)
- [Section 5.2: Equivalent Cauchy sequences](./sec52/)
- [Section 5.3: Construction of the real numbers](./sec53/)
- [Section 5.4: Ordering the reals](./sec54/)
- [Section 5.5: The least upper bound property](./sec55/)
- [Chapter 5 epilogue: Isomorphism with the Mathlib reals](./sec5e/)
- [Section 6.1: Convergence and limit laws](./sec61/)
- [Section 6.2: The extended real number system](./sec62/)
- [Section 6.3: Suprema and Infima of sequences](./sec63/)
- [Section 6.4: Lim inf, lim sup, and limit points](./sec64/)
- [Section 6.5: Some standard limits](./sec65/)
- [Section 6.6: Subsequences](./sec66/)
- [Section 6 epilogue: Connections with Mathlib limits](./sec6e/)
- [Section 7.1: Finite series](./sec71/)
- [Section 7.2: Infinite series](./sec72/)
- [Section 7.3: Sums of non-negative numbers](./sec73/)
- [Section 7.4: Rearrangement of series](./sec74/)
- [Section 7.5: The root and ratio tests](./sec75/)
- [Section 9.1: Subsets of the real line](./sec91/)
- [Section 9.2: The algebra of real-valued functions](./sec92/)
- [Section 9.3: Limiting values of functions](./sec93/)
- [Section 9.4: Continuous functions](./sec94/)
- [Section 9.5: Left and right limits](./sec95/)
- [Section 9.6: The maximum principle](./sec96/)
- [Section 9.7: The intermediate value theorem](./sec97/)
- [Section 9.8: Monotone functions](./sec98/)
- [Section 9.9: Uniform continuity](./sec99/)
- [Section 9.10: Limits at infinity](./sec910/)
- [Section 10.1: Basic definitions](./sec101/)
- [Section 10.2: Local extrema and derivatives](./sec102/)
- [Section 10.3: Monotone functions and derivatives](./sec103/)
- [Section 10.4: The inverse function theorem](./sec104/)
- [Section 10.5: L'Hôpital's rule](./sec105/)
- [Section 11.1: Partitions](./sec111/)
- [Section 11.2: Piecewise constant functions](./sec112/)
- [Section 11.3: Upper and lower Riemann integrals](./sec113/)
- [Appendix A.1: Mathematical statements](./secA1/)
- [Appendix A.2: Implications](./secA2/)
- [Appendix A.3: The structure of proofs](./secA3/)
- [Appendix A.4: Variables and quantifiers](./secA4/)
- [Appendix A.5: Nested quantifiers](./secA5/)
- [Appendix A.6: Some examples of proofs and quantifiers](./secA6/)
- [Appendix A.7: Equality](./secA7/)
