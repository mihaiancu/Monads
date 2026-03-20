namespace BindMonad
/-
# Bind => Monad
-/

class Bind (M : Type → Type) where
  bind : M α → (α → M β) → M β
  pure : α → M α
  bind_pure (x' : M α) : bind x' pure = x'
  pure_bind (x : α) (f' : α → M β) : bind (pure x) f' = f' x
  bind_assoc (x' : M α) (f' : α → M β) (g' : β → M γ) :
        bind (bind x' f') g' = bind x' (fun x => bind (f' x) g')

infixl:55 " >>= " => Bind.bind

variable {M : Type → Type} [Bind M]
   {x : α} {x' : M α} {x'' : M (M α)} {f : α → β} {f' : α → M β} {g' : β → M γ}

#check x' >>= f'

#check Bind.bind_pure x'
#check Bind.pure_bind x f'
#check Bind.bind_assoc x' f' g'

def m (f : α → β) (x' : M α) : M β := x' >>= Bind.pure ∘ f

def join (x'' : M (M α)) : M α := x'' >>= id

#check m f x'
#check join x''

/-
## m is a Functor
-/
theorem m_id (x' : M α) : m id x' = x' := by
  calc m id x'
   _ = x' >>= Bind.pure ∘ id := by rfl
   _ = x' >>= Bind.pure      := by rw [Function.comp_id]
   _ = x'               := by rw [Bind.bind_pure]

theorem m_comp (f : α → β) (g : β → γ) (x' : M α) : m (g ∘ f) x' = (m g ∘ m f) x' := by
  calc m (g ∘ f) x'
   _ = x' >>= Bind.pure ∘ (g ∘ f)                          := by rfl
   _ = x' >>= fun x => (Bind.pure ∘ g) (f x)               := by rfl
   _ = x' >>= fun x => Bind.pure (f x) >>= Bind.pure ∘ g   := by simp [Bind.pure_bind]
   _ = x' >>= fun x => (Bind.pure ∘ f) x >>= Bind.pure ∘ g := by rfl
   _ = x' >>= Bind.pure ∘ f >>= Bind.pure ∘ g              := by simp [Bind.bind_assoc]
   _ = m f x' >>= Bind.pure ∘ g                            := by rfl
   _ = (m g ∘ m f) x'                                      := by rfl

/-
## pure is natural
-/

#check pure

theorem pure_natural (f : α → β) (x : α) : m f (Bind.pure (M:=M) x) = Bind.pure (f x) := by
  calc m f (Bind.pure (M:=M) x)
   _ = Bind.pure (M:=M)  x >>= Bind.pure ∘ f := by rfl
   _ = (Bind.pure ∘ f) x                     := by rw [Bind.pure_bind]
   _ = Bind.pure (f x)                       := by rfl

/-
## join is natural
-/

theorem join_natural (f : α → β) (x'' : M (M α)) : join (m (m f) x'') = m f (join x'') := by
  calc join (m (m f) x'')
   _ = join (x'' >>= Bind.pure ∘ m f)                := by rfl
   _ = x'' >>= Bind.pure ∘ m f >>= id                := by rfl
   _ = x'' >>= fun x' => (Bind.pure ∘ m f) x' >>= id := by rw [Bind.bind_assoc]
   _ = x'' >>= fun x' => Bind.pure (m f x') >>= id   := by rfl
   _ = x'' >>= fun x' => id (m f x')                 := by simp [Bind.pure_bind]
   _ = x'' >>= fun x' => m f x'                      := by rfl
   _ = x'' >>= fun x' => x' >>= Bind.pure ∘ f        := by rfl
   _ = x'' >>= fun x' => id x' >>= Bind.pure ∘ f     := by rfl
   _ = x'' >>= id >>= Bind.pure ∘ f                  := by rw [Bind.bind_assoc]
   _ = m f (x'' >>= id)                              := by rfl
   _ = m f (join x'')                                := by rfl

/-
## join is associative
-/

theorem join_assoc (x''' : M (M (M α))) : join (join x''') = join (m join x''') := by
  calc join (join x''')
   _ = join (x''' >>= id)                                := by rfl
   _ = x''' >>= id >>= id                                := by rfl
   _ = x''' >>= fun x'' => id x'' >>= id                 := by rw [Bind.bind_assoc]
   _ = x''' >>= fun x'' => join x''                      := by rfl
   _ = x''' >>= fun x'' => Bind.pure (join x'') >>= id   := by simp [Bind.pure_bind]
   _ = x''' >>= fun x'' => (Bind.pure ∘ join) x'' >>= id := by rfl
   _ = x''' >>= Bind.pure ∘ join >>= id                  := by rw [Bind.bind_assoc]
   _ = join (x''' >>= Bind.pure ∘ join)                  := by rfl
   _ = join (m join x''')                                := by rfl

/-
## pure is unit
-/

theorem pure_unit (x' : M α) : join (Bind.pure x') = x' ∧ join (m Bind.pure x') = x' := by
  constructor
  · calc join (Bind.pure x')
     _ = Bind.pure  x' >>= id := by rfl
     _ = id x'                := by rw [Bind.pure_bind]
     _ = x'                   := by rfl
  · calc join (m Bind.pure x')
     _ = join (x' >>= Bind.pure ∘ Bind.pure)              := by rfl
     _ = x' >>= Bind.pure ∘ Bind.pure >>= id              := by rfl
     _ = x' >>= fun x => (Bind.pure ∘ Bind.pure) x >>= id := by simp [Bind.bind_assoc]
     _ = x' >>= fun x => Bind.pure (Bind.pure x) >>= id   := by rfl
     _ = x' >>= fun x => id (Bind.pure x)                 := by simp [Bind.pure_bind]
     _ = x' >>= fun x => Bind.pure x                      := by rfl
     _ = x' >>= Bind.pure                                 := by rfl
     _ = x'                                               := by rw [Bind.bind_pure]

end BindMonad

--------------------------------------------------------------------------

namespace MonadBind
/-
# Monad => Bind
-/

class Monad (M : Type → Type) where
  m : (α → β) → (M α → M β)
  pure : α → M α
  join : M (M α) → M α
  m_id (x' : M α) : m id x' = x'
  m_comp (f : α → β) (g : β → γ) (x' : M α) : m (g ∘ f) x' = (m g ∘ m f) x'
  pure_natural (f : α → β) (x : α) : m f (pure x) = pure (f x)
  join_natural (f : α → β) (x'' : M (M α)) : join (m (m f) x'') = m f (join x'')
  join_assoc (x''' : M (M (M α))) : join (join x''') = join (m join x''')
  pure_unit (x' : M α) : join (pure x') = x' ∧ join (m pure x') = x'

variable [Monad M]

open Monad

def andThen (x' : M α) (f : α → M β) : M β := join (m f x')

infixl:55 " >>= " => andThen

/-
## pure is right unit
-/
theorem bind_pure (x' : M α) : x' >>= pure = x' := by
  calc x' >>= pure
   _ = join (m Monad.pure x') := by rfl
   _ = x'                     := by rw [(pure_unit x').2]

/-
## pure is left unit
-/
theorem pure_bind (x : α) (f' : α → M β) : Monad.pure x >>= f' = f' x := by
  calc Monad.pure x >>= f'
   _ = join (m f' (pure x)) := by rfl
   _ = join (pure (f' x))   := by rw [pure_natural f' x]
   _ = f' x                 := by rw [(pure_unit (f' x)).1]

/-
## bind is associative
-/
theorem bind_assoc (x' : M α) (f' : α → M β) (g' : β → M γ) :
    (x' >>= f') >>= g' = x' >>= (fun x => f' x >>= g') := by
  symm
  calc x' >>= (fun x => f' x >>= g')
   _ = join (m (fun x => f' x >>= g') x')                := by rfl
   _ = join (m (fun x => join (m g' (f' x))) x')         := by rfl
   _ = join (m (join ∘ (fun x => m g' (f' x))) x')       := by rfl
   _ = join (((m join) ∘ (m (fun x => m g' (f' x)))) x') := by
                        rw [m_comp (fun x => m g' (f' x)) join x']
   _ = join (m join ((m (fun x => m g' (f' x))) x'))     := by rfl
   _ = join (join ((m (fun x => m g' (f' x))) x'))       := by
                   rw [join_assoc ((m (fun x => m g' (f' x))) x')]
   _ = join (join (m (m g' ∘ f') x'))                    := by rfl
   _ = join (join ((m (m g') ∘ m f') x'))                := by rw [m_comp]
   _ = join (join (m (m g') (m f' x')))                  := by rfl
   _ = join (m g' (join (m f' x')))                      := by rw [join_natural]
   _ = (join (m f' x')) >>= g'                           := by rfl
   _ = (x' >>= f') >>= g'                                := by rfl

end MonadBind

--------------------------------------------------------------------------
------ INSTANCES ------------------------------------------------------------
--------------------------------------------------------------------------

section

instance [BindMonad.Bind M] : MonadBind.Monad M where
  m f x' := BindMonad.Bind.bind x' (BindMonad.Bind.pure ∘ f)
  pure := BindMonad.Bind.pure
  join x'' := BindMonad.Bind.bind x'' id
  m_id := BindMonad.m_id
  m_comp := BindMonad.m_comp
  pure_natural := BindMonad.pure_natural
  join_natural := BindMonad.join_natural
  join_assoc := BindMonad.join_assoc
  pure_unit := BindMonad.pure_unit

open BindMonad.Bind MonadBind.Monad

variable [BindMonad.Bind M] {x' : M α} {x : α} {x'' : M (M α)} {x''' : M (M (M α)) }
         {f : α → β} {g : β → γ} {f' : α → M β} {g' : β → M γ}

#check BindMonad.Bind.pure (M:=M) x
#check MonadBind.Monad.pure (M:=M) x
#check m f x'
#check join x''
#check m_id x'
#check m_comp f g x'
#check pure_natural f x
#check join_natural f x''
#check join_assoc x'''
#check pure_unit x'
#check bind_pure x'
#check pure_bind x f'
#check bind_assoc x' f' g'

end

--------------------------------------------------------------------------

section

#check MonadBind.Monad

instance [MonadBind.Monad M] : BindMonad.Bind M where
  bind x' f' := MonadBind.Monad.join (MonadBind.Monad.m f' x')
  pure := MonadBind.Monad.pure
  bind_pure := MonadBind.bind_pure
  pure_bind := MonadBind.pure_bind
  bind_assoc := MonadBind.bind_assoc

open BindMonad.Bind MonadBind.Monad

variable [BindMonad.Bind M] {x' : M α} {x : α} {x'' : M (M α)} {x''' : M (M (M α)) }
         {f : α → β} {g : β → γ} {f' : α → M β} {g' : β → M γ}

#check BindMonad.Bind.pure (M:=M) x
#check MonadBind.Monad.pure (M:=M) x
#check m f x'
#check join x''
#check m_id x'
#check m_comp f g x'
#check pure_natural f x
#check join_natural f x''
#check join_assoc x'''
#check pure_unit x'
#check bind_pure x'
#check pure_bind x f'
#check bind_assoc x' f' g'

end
