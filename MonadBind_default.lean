import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Types.Basic

namespace BindMonad
/-
# Bind => Monad
-/
variable [Monad M] [LawfulMonad M]
 {x : α} {x' : M α} {f : α → β} {f' : α → M β} {g' : β → M γ}

#check bind_pure x' -- x' >>= pure = x'

#check pure_bind x f' -- pure x >>= f' = f' x

#check bind_assoc x' f' g' -- x' >>= f' >>= g' = x' >>= fun x ↦ f' x >>= g'

def m (f : α → β) (x' : M α) : M β := x' >>= pure ∘ f

def join (x'' : M (M α)) : M α := x'' >>= id

/-
## m is a Functor
-/
theorem m_id (x' : M α) : m id x' = x' := by
  calc m id x'
   _ = x' >>= pure ∘ id := by rfl
   _ = x' >>= pure      := by trivial--rw [Function.comp_id]
   _ = x'               := by rw [bind_pure]

theorem m_comp (f : α → β) (g : β → γ) (x' : M α) : m (g ∘ f) x' = (m g ∘ m f) x' := by
  calc m (g ∘ f) x'
   _ = x' >>= pure ∘ (g ∘ f)                     := by rfl
   _ = x' >>= fun x => (pure ∘ g) (f x)          := by rfl
   _ = x' >>= fun x => pure (f x) >>= pure ∘ g   := by simp [pure_bind]
   _ = x' >>= fun x => (pure ∘ f) x >>= pure ∘ g := by rfl
   _ = x' >>= pure ∘ f >>= pure ∘ g              := by simp [bind_assoc]
   _ = m f x' >>= pure ∘ g                       := by rfl
   _ = (m g ∘ m f) x'                            := by rfl

/-
## pure is natural
-/

theorem pure_natural (f : α → β) (x : α) : m f (@pure M _ _ x) = pure (f x) := by
  calc m f (@pure M _ _ x)
   _ = pure x >>= pure ∘ f := by rfl
   _ = (pure ∘ f) x        := by rw [pure_bind x (pure ∘ f)]
   _ = pure (f x)          := by rfl

/-
## join is natural
-/

theorem join_natural (f : α → β) (x'' : M (M α)) : join (m (m f) x'') = m f (join x'') := by
  calc join (m (m f) x'')
   _ = join (x'' >>= pure ∘ m f)                := by rfl
   _ = x'' >>= pure ∘ m f >>= id                := by rfl
   _ = x'' >>= fun x' => (pure ∘ m f) x' >>= id := by rw [bind_assoc]
   _ = x'' >>= fun x' => pure (m f x') >>= id   := by rfl
   _ = x'' >>= fun x' => id (m f x')            := by simp [pure_bind]
   _ = x'' >>= fun x' => m f x'                 := by rfl
   _ = x'' >>= fun x' => x' >>= pure ∘ f        := by rfl
   _ = x'' >>= fun x' => id x' >>= pure ∘ f     := by rfl
   _ = x'' >>= id >>= pure ∘ f                  := by rw [bind_assoc]
   _ = m f (x'' >>= id)                         := by rfl
   _ = m f (join x'')                           := by rfl

/-
## join is associative
-/

theorem join_assoc (x''' : M (M (M α))) : join (join x''') = join (m join x''') := by
  calc join (join x''')
   _ = join (x''' >>= id)                           := by rfl
   _ = x''' >>= id >>= id                           := by rfl
   _ = x''' >>= fun x'' => id x'' >>= id            := by rw [bind_assoc]
   _ = x''' >>= fun x'' => join x''                 := by rfl
   _ = x''' >>= fun x'' => pure (join x'') >>= id   := by simp [pure_bind]
   _ = x''' >>= fun x'' => (pure ∘ join) x'' >>= id := by rfl
   _ = x''' >>= pure ∘ join >>= id                  := by rw [bind_assoc]
   _ = join (x''' >>= pure ∘ join)                  := by rfl
   _ = join (m join x''')                           := by rfl

/-
## pure is unity
-/

theorem pure_unity (x' : M α) : join (pure x') = x' ∧ join (m pure x') = x' := by
  constructor
  · calc join (pure x')
     _ = pure x' >>= id := by rfl
     _ = id x'          := by rw [pure_bind]
     _ = x'             := by rfl
  · calc join (m pure x')
     _ = join (x' >>= pure ∘ pure)              := by rfl
     _ = x' >>= pure ∘ pure >>= id              := by rfl
     _ = x' >>= fun x => (pure ∘ pure) x >>= id := by rw [bind_assoc]
     _ = x' >>= fun x => pure (pure x) >>= id   := by rfl
     _ = x' >>= fun x => id (pure x)            := by simp [pure_bind]
     _ = x' >>= fun x => pure x                 := by rfl
     _ = x' >>= pure                            := by rfl
     _ = x'                                     := by rw [bind_pure]

end BindMonad


--------------------------------------------------------------------------
namespace MonadBind
/-
# Monad => Bind
-/

open CategoryTheory

variable {M : Monad Type} {x : α} {x' : M.obj α} {x'' : M.obj (M.obj α)}
         {f : α ⟶ β} {g : β → γ} {f' : α → M.obj β} {g' : β → M.obj γ}

#check M.obj
#check M.map f

#check M.map_id α -- M.map id = id
#check M.map_comp f g -- M.map (f ≫ g) = M.map f ≫ M.map g

#check f ≫ g
#check types_comp f g --  f ≫ g = g ∘ f
#check types_id (X:=α) -- 𝟙 α = id

abbrev pure {α : Type} := M.η.app α

abbrev join {α : Type} := M.μ.app α

#check pure
#check Functor.id_obj α  -- (𝟭 Type).obj α = α

#check join
#check Functor.comp_obj M.toFunctor M.toFunctor α
-- (M.toFunctor ⋙ M.toFunctor).obj α = M.obj (M.obj α)

#check M.unit_naturality (f:=f) -- f ≫ pure = pure ≫ M.map f
#check M.mu_naturality (f:=f) -- M.map (M.map f) ≫ join = join ≫ M.map f

#check M.assoc α -- M.map join ≫ join = join ≫ join
#check M.left_unit α -- pure ≫ join = id
#check M.right_unit α -- M.map pure ≫ join = id


def andThen (x' : M.obj α) (f' : α → M.obj β) : M.obj β := join (M.map f' x')

infixl:55 " >>= " => andThen

#check x' >>= f'


/-
## pure is right unity
-/
theorem bind_pure (x' : M.obj α) : x' >>= pure = x' := by
  calc x' >>= pure
   _ = join (M.map pure x')            := by rfl
   _ = (M.map pure ≫ join) x'         := by rfl
   _ = (𝟙 (M.obj ((𝟭 Type).obj α))) x' := by rw [M.right_unit]

/-
## pure is left unity
-/
theorem pure_bind (x : α) (f' : α → M.obj β) : pure x >>= f' = f' x := by
  calc pure x >>= f'
   _ = join (M.map f' (pure x))                := by rfl
   _ = join ((pure ≫ M.map f') x)             := by rfl
   _ = join ((f' ≫ pure) x)                   := by rw [← M.unit_naturality]
   _ = (f' ≫ pure ≫ join) x                  := by rfl
   _ = (f' ≫ ( 𝟙 ((𝟭 Type).obj (M.obj β)))) x := by rw [M.left_unit]

#check M.map_comp
#check M.map_comp f g
#check (f' ≫ M.map g')
#check M.map_comp (f' ≫ M.map g') join
#check M.assoc

/-
## bind is associative
-/
theorem bind_assoc (x' : M.obj α) (f' : α → M.obj β) (g' : β → M.obj γ) :
    (x' >>= f') >>= g' = x' >>= (fun x => f' x >>= g') := by
  symm
  calc x' >>= (fun x => f' x >>= g')
   _ = join (M.map (fun x => f' x >>= g') x')                  := by rfl
   _ = join (M.map (fun x => join (M.map g' (f' x))) x')       := by rfl
   _ = join (M.map ((fun x => M.map g' (f' x)) ≫ join) x')    := by rfl
   _ = join (M.map ((f' ≫ M.map g') ≫ join) x')              := by rfl
   _ = join ((M.map (f' ≫ M.map g') ≫ M.map join) x')        := by rw [M.map_comp]
   _ = join ((M.map f' ≫ M.map (M.map g') ≫ M.map join) x')  := by rw [M.map_comp]; rfl
   _ = (M.map f' ≫ M.map (M.map g') ≫ M.map join ≫ join) x' := by rfl
   _ = (M.map f' ≫ M.map (M.map g') ≫ join ≫ join) x'       := by rw [M.assoc]
   _ = (M.map f' ≫ (M.map (M.map g') ≫ join) ≫ join) x'     := by rfl
   _ = (M.map f' ≫ (join ≫ M.map g') ≫ join) x'             := by rw [Monad.mu_naturality]
   _ = (M.map f' ≫ join ≫ M.map g' ≫ join) x'               := by rfl
   _ = join ((M.map f' ≫ join ≫ M.map g') x')                := by rfl
   _ = join (M.map g' ((M.map f' ≫ join) x'))                 := by rfl
   _ = (M.map f' ≫ join) x'>>= g'                             := by rfl
   _ = x' >>= f' >>= g'                                        := by rfl

end MonadBind
