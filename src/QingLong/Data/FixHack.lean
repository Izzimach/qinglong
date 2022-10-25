
namespace FixHack

-- compiler doesn't prove well founded-ness for normal fix, thus we use this hack

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}


unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
    F x fun y _ => impl hwf F y


--set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end FixHack