module
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# Preserving fixed-space parameters through the original central cover

An injective actor marking preserves relative indices. A surjective module
map whose fixed vectors lift identifies the fixed spaces for every subgroup
of the actor. Thus the source A_k family transfers to the actual quotient
representation, retaining the full central kernel. ActorRecognition.Source
applies this to the chosen G₂ module and its original automizer.
Source: Aschbacher--Smith B.4.6(7,9), printed pp.88--89.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
variable {H J X Y : Type*} [Group H] [Group J]
  [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Exact lifting of fixed vectors carries the source family through a
surjective module projection and an injective actor marking. -/
theorem family_range_of_fixed_lifting
    (σ : Representation (ZMod 2) H X) (ρ : Representation (ZMod 2) J Y)
    {A : Subgroup H} (j : A →* J) (hj : Function.Injective j)
    (q : X →ₗ[ZMod 2] Y) (hq : Function.Surjective q)
    (he : ∀ a : A, ∀ x, q (σ a x) = ρ (j a) (q x))
    (hlift : ∀ a : A, ∀ x, ρ (j a) (q x) = q x → σ a x = x)
    {k : ℕ} (hA : A ∈ fixedSpaceFamily σ k) :
    j.range ∈ fixedSpaceFamily ρ k := by
  let := hA.2.1.2
  refine ⟨hA.1,⟨?_,IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective⟩,?_⟩
  · intro hb
    apply hA.2.1.1
    apply le_antisymm ?_ bot_le
    intro a ha
    have heq : j ⟨a,ha⟩ = 1 := by
      have hh : j ⟨a,ha⟩ ∈ j.range := ⟨⟨a,ha⟩,rfl⟩
      rwa [hb,mem_bot] at hh
    exact congrArg Subtype.val (hj (heq.trans (map_one j).symm))
  · intro B hB hindex
    let C := (B.comap j).map A.subtype
    have hCA : C ≤ A := map_subtype_le _
    have hidx : C.relIndex A = B.relIndex j.range := by
      have hh := relIndex_map_map_of_injective (B.comap j) (⊤ : Subgroup A) A.subtype_injective
      simpa only [←MonoidHom.range_eq_map,A.range_subtype,relIndex_top_right,index_comap] using hh
    have hfix := hA.2.2 C hCA (hidx.symm ▸ hindex)
    apply le_antisymm (ChapterE.fixedSpace_antitone ρ hB)
    intro y hy
    obtain ⟨x,rfl⟩ := hq y
    have hx : x ∈ fixedSpace σ C := by
      rintro ⟨c,hc⟩
      obtain ⟨a,ha,rfl⟩ := hc
      exact hlift a x (hy ⟨j a,ha⟩)
    rw [←hfix] at hx
    rintro ⟨a,⟨b,rfl⟩⟩
    exact (he b x).symm.trans (congrArg q (hx b))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
