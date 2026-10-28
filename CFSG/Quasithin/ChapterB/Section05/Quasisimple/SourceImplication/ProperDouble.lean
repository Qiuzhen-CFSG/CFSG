module
public import Theory.Representation.ProperDouble
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# One natural copy inside a doubled natural module

A nonzero proper invariant subspace of two copies of a simple natural module
is one natural copy. The coordinate projection proof retains the given group
marking. This is the one-copy image step of the original fixed-layer argument,
Aschbacher–Smith13.7.16(2), printed p.944.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem repeated_double_proper_submodule_equiv (F : BinaryField) {d : ℕ} (hd : 2 ≤ d)
    (a : ActionEquiv ρ (repeated (linearNatural F d) 2))
    (N : Subrepresentation ρ) (hne : N ≠ ⊥) (hproper : N ≠ ⊤) :
    Nonempty (N.toRepresentation.Equiv ((linearNatural F d).comp a.groupEquiv.toMonoidHom)) := by
  let π := (linearNatural F d).comp a.groupEquiv.toMonoidHom
  let b : ActionEquiv π (linearNatural F d) :=
    ⟨a.groupEquiv,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  let : IsIrreducible π := ExtensionConsequences.irreducible_of_equiv b
    (ExtensionConsequences.linearNatural_irreducible F hd)
  let f : N.toSubmodule →ₗ[ZMod 2] ((Fin d → F.Carrier) × (Fin d → F.Carrier)) :=
    { toFun := fun v => (a.linearEquiv v.val 0,a.linearEquiv v.val 1)
      map_add' := by intros; apply Prod.ext <;> simp
      map_smul' := by intros; apply Prod.ext <;> simp }
  let i : N.toRepresentation.IntertwiningMap (Representation.prod π π) :=
    f.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      apply Prod.ext
      · exact congrFun (a.intertwines g v.val) 0
      · exact congrFun (a.intertwines g v.val) 1)
  have hi : Function.Injective i := by
    intro v w he
    apply Subtype.ext
    apply a.linearEquiv.injective
    funext j
    fin_cases j
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have hn : i ≠ 0 := by
    intro hz
    apply hne
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have he := hi (show i ⟨v,hv⟩ = i 0 by rw [hz]; rfl)
    exact Subtype.ext_iff.mp he
  have hp : ¬ Function.Surjective i := by
    intro hs
    apply hproper
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨w,hw⟩ := hs (a.linearEquiv v 0,a.linearEquiv v 1)
    have he : w.val = v := by
      apply a.linearEquiv.injective
      funext j
      fin_cases j
      · exact congrArg Prod.fst hw
      · exact congrArg Prod.snd hw
    exact he ▸ w.property
  exact Representation.equiv_of_injective_map_to_proper_double i hi hn hp
end CFSG.Quasithin.ChapterB.QuasisimpleSource
