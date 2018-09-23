Idempotent : (a -> a) -> a -> Type
Idempotent f a = f (f a) = f a

Involution : (a -> a) -> a -> Type
Involution f a = f (f a) = a

idempInvol : Idempotent f a -> Involution f a -> f a = a
idempInvol prf prf' = trans (sym prf) prf'
