# easycrypt-zk-code




lemma nosmt modzMml: forall (m n d : int), m %% d * n %% d = m * n %% d.
lemma nosmt modzMmr: forall (m n d : int), m * (n %% d) %% d = m * n %% d.
lemma nosmt modzMm:
  forall (m n d : int), m %% d * (n %% d) %% d = m * n %% d.
lemma nosmt modzNm: forall (m d : int), (- m %% d) %% d = (-m) %% d.
lemma nosmt mulz_modr:
  forall (p m d : int), 0 < p => p * (m %% d) = p * m %% (p * d).
lemma nosmt mulz_modl:
  forall (p m d : int), 0 < p => m %% d * p = m * p %% (d * p).

