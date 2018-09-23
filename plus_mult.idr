plus_commutes_Z : plus 0 m = plus m 0
plus_commutes_Z {m=Z} = Refl
plus_commutes_Z {m=(S k)} = let rec = plus_commutes_Z {m=k} in
                                rewrite rec in Refl

plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_S k Z = Refl
plus_commutes_S k (S j) = let rec = plus_commutes_S k j in
                             rewrite rec in Refl

plus_commutes : (n, m : Nat) -> plus n m = plus m n
plus_commutes Z m = plus_commutes_Z
plus_commutes (S k) m = rewrite plus_commutes k m in (plus_commutes_S k m)

plus_assoc : (n, m, p : Nat) -> plus n (plus m p) = plus (plus n m) p
plus_assoc Z m p = Refl
plus_assoc (S k) m p = rewrite plus_assoc k m p in Refl

mult_commutes : (n, m : Nat) -> n*m = m*n
mult_commutes Z Z = Refl
mult_commutes Z (S k) = rewrite mult_commutes Z k in Refl
mult_commutes (S k) Z = rewrite mult_commutes k Z in Refl
mult_commutes (S k) (S j) = rewrite mult_commutes k (S j) in
                            rewrite mult_commutes j (S k) in
                            rewrite mult_commutes j    k  in
                            rewrite plus_assoc j k (mult k j) in
                            rewrite plus_assoc k j (mult k j) in
                            rewrite plus_commutes j k in Refl

plus_distributes : (a, b, c : Nat) -> mult a (plus b c) = plus (mult a b) (mult a c)
plus_distributes Z b c = Refl
plus_distributes (S k) Z c = rewrite mult_commutes k Z in Refl
plus_distributes (S k) (S j) Z = rewrite plus_commutes j Z in
                                 rewrite mult_commutes k Z in
                                 rewrite plus_commutes (plus j (mult k (S j))) Z in
                                         Refl
plus_distributes (S k) (S j) (S i) = rewrite mult_commutes k (S j) in
                                     rewrite plus_commutes j (S i) in
                                     rewrite mult_commutes k (S i) in
                                     rewrite mult_commutes k (S (S (plus i j))) in
                                     rewrite plus_commutes (plus j (plus k (mult j k))) (S (plus i (plus k (mult i k)))) in
                                     rewrite mult_commutes (plus i j) k in
                                     rewrite plus_distributes k i j in
                                     rewrite plus_assoc (i+(k+i*k)) j (k+j*k) in
                                     rewrite plus_commutes (i+(k+i*k)) j in
                                     rewrite plus_assoc j i (k+i*k) in
                                     rewrite plus_commutes j i in
                                     rewrite mult_commutes k i in
                                     rewrite mult_commutes k j in
                                     rewrite plus_commutes ((i+j)+(k+i*k)) (k+j*k) in
                                     rewrite plus_assoc (k+j*k) (i+j) (k+i*k) in
                                     rewrite plus_commutes ((k+j*k)+(i+j)) (k+i*k) in
                                     rewrite plus_assoc (k+i*k) (k+j*k) (i+j) in
                                     rewrite plus_commutes ((k+i*k)+(k+j*k)) (i+j) in
                                     rewrite plus_commutes k (j*k) in
                                     rewrite plus_assoc (k + i*k) (j*k) k in
                                     rewrite sym (plus_assoc k (i*k) (j*k)) in
                                     rewrite plus_commutes (k+(i*k+j*k)) k in
                                             Refl

mult_assoc : (n, m, p : Nat) -> n*(m*p) = (n*m)*p
mult_assoc Z m p = Refl
mult_assoc (S k) Z p = rewrite mult_commutes k 0 in Refl
mult_assoc (S k) (S j) Z = rewrite mult_commutes j 0 in
                           rewrite mult_commutes k 0 in
                           rewrite mult_commutes (plus j (mult k (S j))) 0 in
                                   Refl
mult_assoc (S k) (S j) (S i) = rewrite mult_commutes j (S i) in
                               rewrite mult_commutes k (S j) in
                               rewrite mult_commutes (plus j (plus k (mult j k))) (S i) in
                               rewrite mult_commutes k (S (plus i (plus j (mult i j)))) in
                               rewrite plus_distributes i j (k+j*k) in
                               rewrite plus_distributes i k (j*k) in
                               rewrite sym (plus_assoc j (k+j*k) (i*j+(i*k+(i*(j*k))))) in
                               rewrite sym (plus_assoc k (j*k) ((i*j)+(i*k+i*(j*k)))) in
                               rewrite plus_commutes (i*j) (i*k + i*(j*k)) in
                               rewrite plus_assoc (j*k) (i*k + i*(j*k)) (i*j) in
                               rewrite plus_assoc (j*k) (i*k) (i*(j*k)) in
                               rewrite plus_commutes (j*k) (i*k) in
                               rewrite sym (plus_assoc (i*k) (j*k) (i*(j*k))) in
                               rewrite mult_assoc i j k in
                               rewrite mult_commutes (i*j) k in
                               rewrite mult_commutes j k in
                               rewrite sym (plus_distributes k j (i*j)) in
                               rewrite mult_commutes i k in
                               rewrite sym (plus_distributes k i (j + i*j)) in
                               rewrite plus_assoc k (k*(i + (j + i*j))) (i*j) in
                               rewrite mult_commutes k (i + (j + i*j)) in
                               rewrite plus_commutes (k + ((i + (j + i*j))*k)) (i*j) in
                               rewrite plus_assoc i j (i*j + (k + ((i + (j + i*j))*k))) in
                               rewrite plus_assoc (i+j) (i*j) (k + ((i + (j + i*j))*k)) in
                               rewrite sym (plus_assoc i j (i*j)) in
                                       Refl

succInjective : (n, m : Nat) -> S n = S m -> n = m
succInjective Z Z prf = Refl
succInjective Z (S _) Refl impossible
succInjective (S _) Z Refl impossible
succInjective (S j) (S j) Refl = Refl
