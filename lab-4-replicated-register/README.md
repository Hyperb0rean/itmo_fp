

### Lab 4 - Linearizable Replicated register 

Для работы будет использован фреймоврк [Verdi](https://github.com/uwplse/verdi)

В планах предоставить имплементацию алгоритма [ABD (linearizable register algorithm)](https://groups.csail.mit.edu/tds/papers/Attiya/TM-423.pdf)

Возможные утверждения для доказательства предоставлены в статье:
Линеризуемость, корректность состояния регистра на разных репликах, 
оценка на отказоустойчивостьь.

Сущности:
Клиент, N  Реплик с регистром


Proof of Work для фреймворка:
[Examples](https://github.com/uwplse/verdi/tree/master/theories/Systems)
[Raft](https://github.com/uwplse/verdi-raft)