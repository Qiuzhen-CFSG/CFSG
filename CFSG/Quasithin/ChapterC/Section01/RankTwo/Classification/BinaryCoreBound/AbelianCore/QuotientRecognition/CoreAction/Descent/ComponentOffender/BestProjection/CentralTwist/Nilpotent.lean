module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Head
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions

/-!
# A square-zero endomorphism forces homogeneous natural coordinates

In dimension at most six, a nonzero square-zero endomorphism commuting with
SL₃(2) has image of dimension at most three. Surjective equivariant maps
preserve full commutator generation, so the checked irreducible catalogue
identifies this image as natural or dual-natural. Rank-nullity makes image
and kernel equal. The endomorphism identifies the quotient with its image;
unconditional homogeneous splitting then gives actual two-copy coordinates.

This is a local algebraic reduction for the binary component transfer near
Aschbacher–Smith C.1.31–34, printed pp.135–137. The homogeneous splitting
input proves the relevant binary specialization of B.4.9 independently,
without an FF-module premise.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender.BestProjection.CentralTwist
open AbelianCore.QuotientRecognition.ExtensionControl
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private theorem full_of_surjective_intertwiner
    {K X Y : Type*} [Group K] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) K X) (σ : Representation (ZMod 2) K Y)
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    subspaceCommutator σ ⊤ ⊤ = ⊤ := by
  have hm : subspaceCommutator ρ ⊤ ⊤ ≤
      (subspaceCommutator σ ⊤ ⊤).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    change f (ρ g v - v) ∈ subspaceCommutator σ ⊤ ⊤
    rw [map_sub, he]
    exact Submodule.subset_span ⟨g, trivial, f v, trivial, rfl⟩
  apply top_unique
  intro y _
  obtain ⟨x,rfl⟩ := hf y
  apply hm
  rw [hfull]
  trivial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem natural_of_full_finrank_le_three [Nontrivial V]
    (ρ : Representation (ZMod 2) SL V)
    (hd : Module.finrank (ZMod 2) V ≤ 3)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) : NaturalOrDual ρ := by
  obtain ⟨N, hN, _⟩ := exists_natural_head ρ (by omega) hfull
  have hq := hN.finrank
  have hr := N.toSubmodule.finrank_quotient_add_finrank
  have hn : N.toSubmodule = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hi : Function.Injective N.toSubmodule.mkQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mkQ, hn]
  let e : ρ.Equiv N.quotientRepresentation :=
    Representation.Equiv.mk (LinearEquiv.ofBijective N.toSubmodule.mkQ
      ⟨hi, N.toSubmodule.mkQ_surjective⟩) (by intro g; rfl)
  rcases hN with hN | hN <;> obtain ⟨eN⟩ := hN
  · exact Or.inl ⟨e.trans eN⟩
  · exact Or.inr ⟨e.trans eN⟩

/-- A nonzero square-zero component endomorphism in dimension at most six
forces two equal natural composition factors and hence a split homogeneous
module. No offender assumption enters this conclusion. -/
theorem homogeneous_of_square_zero
    (ρ : Representation (ZMod 2) SL V)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hd : Module.finrank (ZMod 2) V ≤ 6)
    (T : Module.End (ZMod 2) V)
    (hT : T ≠ 0) (hTT : T.comp T = 0)
    (hcomm : ∀ g v, T (ρ g v) = ρ g (T v)) :
    ∃ a : SL ≃* SL,
      Nonempty (ρ.Equiv (Representation.prod (BinaryLinearThree.W.comp a.toMonoidHom)
        (BinaryLinearThree.W.comp a.toMonoidHom))) := by
  let U : Subrepresentation ρ := {
    toSubmodule := LinearMap.range T
    apply_mem_toSubmodule g := by
      rintro _ ⟨v, rfl⟩
      exact ⟨ρ g v, hcomm g v⟩ }
  have hUfull : subspaceCommutator U.toRepresentation ⊤ ⊤ = ⊤ :=
    full_of_surjective_intertwiner ρ U.toRepresentation T.rangeRestrict
      (by rintro ⟨w,v,rfl⟩; exact ⟨v,rfl⟩) (fun g v => Subtype.ext (hcomm g v)) hfull
  have hUn : U.toSubmodule ≠ ⊥ := by
    change LinearMap.range T ≠ ⊥
    intro h
    apply hT
    exact LinearMap.range_eq_bot.mp h
  let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hUn
  have hUk : U.toSubmodule ≤ LinearMap.ker T := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.congr_fun hTT v
  have hdim := T.finrank_range_add_finrank_ker
  have hle := Submodule.finrank_mono hUk
  have hUdim : Module.finrank (ZMod 2) U.toSubmodule ≤ 3 := by
    change Module.finrank (ZMod 2) (LinearMap.range T) ≤ 3
    change Module.finrank (ZMod 2) (LinearMap.range T) ≤ _ at hle
    omega
  have hnatural := natural_of_full_finrank_le_three U.toRepresentation hUdim hUfull
  have hthree := hnatural.finrank
  have heq : U.toSubmodule = LinearMap.ker T := by
    apply Submodule.eq_of_le_of_finrank_eq hUk
    change Module.finrank (ZMod 2) (LinearMap.range T) = _
    change Module.finrank (ZMod 2) (LinearMap.range T) = 3 at hthree
    change Module.finrank (ZMod 2) (LinearMap.range T) ≤ _ at hle
    omega
  let f : (V ⧸ U.toSubmodule) →ₗ[ZMod 2] U.toSubmodule :=
    U.toSubmodule.liftQ T.rangeRestrict (by
      intro v hv
      apply Subtype.ext
      exact hUk hv)
  have hf (v : V) : f (U.toSubmodule.mkQ v) = T.rangeRestrict v := rfl
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    induction w using Submodule.Quotient.induction_on with | _ v =>
      apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr
      rw [heq]
      exact congrArg Subtype.val hw
  have hfs : Function.Surjective f := by
    rintro ⟨w,v,rfl⟩
    exact ⟨U.toSubmodule.mkQ v, rfl⟩
  let e : U.quotientRepresentation.Equiv U.toRepresentation :=
    Representation.Equiv.mk (LinearEquiv.ofBijective f ⟨hfi,hfs⟩) (by
      intro g
      apply LinearMap.ext
      intro w
      induction w using Submodule.Quotient.induction_on with | _ v =>
        exact Subtype.ext (hcomm g v))
  obtain ⟨a,⟨eU⟩⟩ := hnatural.marked
  exact ⟨a, homogeneous_splitting ρ U a ⟨eU⟩ ⟨e.trans eU⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender.BestProjection.CentralTwist
