module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.OuterInvolutionRank
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Eliminating exchanged summands in B.5.1, case (II)

A subspace disjoint from its translate injects into the quotient by the
translating actor's fixed space. The full automorphism centralizer bound
therefore forces an offender containing an outer involution to attain this
fixed-codimension bound. Its fixed space equals that of the involution.
The fixed diagonal vectors then show that every offender element preserving
the original summand fixes it pointwise.

For a faithful marked PSL₄(2) or PSL₅(2) action, the inner intersection is
therefore trivial. The offender would embed in the cyclic outer quotient,
contradicting its required rank. Applying this to the actual offender-generated
group gives `whole_of_marked_outer_summands`, the G = L step in source case
(II). Construction of the faithful marked group action and the natural socle
summands remains part of the classification induction; it is not assumed
in the final classification statement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
case (II), printed p.101. All centralizers below lie in the full automorphism
group, and the outer quotient is the literal quotient by inner automorphisms.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)


/-- A disjoint translate detects every dimension of the original subspace. -/
theorem finrank_le_fixedCodim_of_disjoint_translate (I : Submodule (ZMod 2) V) (b : G)
    (hdis : Disjoint I (I.map (ρ b))) :
    Module.finrank (ZMod 2) I ≤ fixedCodim ρ (zpowers b) := by
  let q : I →ₗ[ZMod 2] V ⧸ fixedSpace ρ (zpowers b) :=
    (fixedSpace ρ (zpowers b)).mkQ.comp I.subtype
  apply LinearMap.finrank_le_finrank_of_injective (f := q)
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro x hx
  have hfix : (x : V) ∈ fixedSpace ρ (zpowers b) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  have hxb : ρ b x = x := (mem_fixedSpace_zpowers_iff ρ b x).mp hfix
  have hi : (x : V) ∈ I.map (ρ b) := ⟨x, x.property, hxb⟩
  exact Subtype.ext ((Submodule.disjoint_def.mp hdis) x x.property hi)

/-- Attaining that lower bound identifies the literal fixed spaces. -/
theorem fixedSpace_eq_of_disjoint_translate (I : Submodule (ZMod 2) V)
    {A : Subgroup G} (hA : IsOffender ρ A) (hr : rank A ≤ Module.finrank (ZMod 2) I)
    {b : G} (hb : b ∈ A) (hdis : Disjoint I (I.map (ρ b))) :
    fixedSpace ρ A = fixedSpace ρ (zpowers b) := by
  have hle := fixedSpace_antitone ρ (zpowers_le.mpr hb)
  have hlow := finrank_le_fixedCodim_of_disjoint_translate ρ I b hdis
  have hdim := Submodule.finrank_mono hle
  have hcodA := fixedCodim_add_finrank ρ A
  have hcodb := fixedCodim_add_finrank ρ (zpowers b)
  have hoff := hA.2
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

/-- The fixed diagonal forces every summand-preserving offender element to fix it. -/
theorem offender_fixes_preserved_summand (I : Submodule (ZMod 2) V)
    {A : Subgroup G} (hA : IsOffender ρ A) (hr : rank A ≤ Module.finrank (ZMod 2) I)
    {b : G} (hb : b ∈ A) (hdis : Disjoint I (I.map (ρ b)))
    {c : G} (hc : c ∈ A) (hcI : c ∈ subspaceStabilizer ρ I) :
    ∀ v ∈ I, ρ c v = v := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hb2 : b * b = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hcb : c * b = b * c :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨c, hc⟩ ⟨b, hb⟩)
  have hfixed := fixedSpace_eq_of_disjoint_translate ρ I hA hr hb hdis
  intro v hv
  have hdiag : v + ρ b v ∈ fixedSpace ρ (zpowers b) := by
    apply (mem_fixedSpace_zpowers_iff ρ b _).mpr
    rw [map_add, ← Module.End.mul_apply, ← map_mul, hb2, map_one,
      Module.End.one_apply, add_comm]
  have he : ρ c (v + ρ b v) = v + ρ b v := (hfixed ▸ hdiag) ⟨c, hc⟩
  have he' : (ρ c v - v) + ρ b (ρ c v - v) = 0 := by
    rw [map_add, ← Module.End.mul_apply, ← map_mul, hcb, map_mul,
      Module.End.mul_apply] at he
    rw [map_sub]
    calc
      _ = (ρ c v + ρ b (ρ c v)) - (v + ρ b v) := by abel
      _ = 0 := sub_eq_zero.mpr he
  have hdI : ρ c v - v ∈ I := I.sub_mem ((hcI v).mpr hv) hv
  have hdmap : ρ c v - v ∈ I.map (ρ b) := by
    refine ⟨-(ρ c v - v), I.neg_mem hdI, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left he').symm
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hdis) _ hdI hdmap)

omit [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
private theorem elementary_rank_le_of_embedding [Finite G] {A : Subgroup G}
    (hA : IsElementaryTwo A) {H : Type*} [Group H] [Finite H]
    (f : A →* H) (hf : Function.Injective f) : rank A ≤ primeRank 2 H := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (fun a => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property))
    hA.card_eq_two_pow_rank f hf

omit [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
/-- Embed the actual elementary actor in the full outer-involution centralizer. -/
theorem rank_le_four_of_outer_actor [Finite G] {d : ℕ} (hd : d = 4 ∨ d = 5)
    (φ : G →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)))
    (hφ : Function.Injective φ) {A : Subgroup G} (hA : IsElementaryTwo A)
    {b : G} (hb : b ∈ A)
    (hout : φ b ∉ MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2))) :
    rank A ≤ 4 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  have hb2 : (φ b) ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb, map_one]
  have hbn : φ b ≠ 1 := fun he => hout (he ▸ Subgroup.one_mem _)
  have ht : orderOf (φ b) = 2 := orderOf_eq_prime hb2 hbn
  let C := centralizer ({φ b} : Set (MulAut
    (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2))))
  let j : A →* C := (φ.comp A.subtype).codRestrict C (by
    intro a
    apply mem_centralizer_singleton_iff.mpr
    change φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := A)).comm a ⟨b, hb⟩)))
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hφ (congrArg Subtype.val h))
  exact (elementary_rank_le_of_embedding hA j hj).trans
    (OuterInvolutionRank.psl_outer_involution_centralizer_rank_le_four d hd (φ b) ht hout)

/-- Faithfulness on the preserved summand excludes an outer exchanging offender. -/
theorem not_offender_of_outer_disjoint_translate [Finite G]
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (φ : G →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)))
    (hφ : Function.Injective φ) (I : Submodule (ZMod 2) V)
    (hdim : d ≤ Module.finrank (ZMod 2) I)
    (hstable : ∀ g, φ g ∈ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) →
      g ∈ subspaceStabilizer ρ I)
    (hfaith : ∀ g, φ g ∈ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) →
      (∀ v ∈ I, ρ g v = v) → g = 1)
    {A : Subgroup G} (hA : IsElementaryTwo A) {b : G} (hb : b ∈ A)
    (hout : φ b ∉ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)))
    (hdis : Disjoint I (I.map (ρ b))) : ¬ IsOffender ρ A := by
  intro hoff
  have hr4 := rank_le_four_of_outer_actor hd φ hφ hA hb hout
  have hrI : rank A ≤ Module.finrank (ZMod 2) I := by omega
  let L := Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)
  let ψ : A →* MulAut.Outer L :=
    ((QuotientGroup.mk' (MulAut.innerSubgroup L)).comp φ).comp A.subtype
  have hψ : Function.Injective ψ := by
    apply (MonoidHom.ker_eq_bot_iff ψ).mp
    apply bot_unique
    intro a ha
    have hai : φ a ∈ MulAut.innerSubgroup L := (QuotientGroup.eq_one_iff _).mp ha
    exact Subtype.ext (hfaith a hai
      (offender_fixes_preserved_summand ρ I hoff hrI hb hdis a.property (hstable a hai)))
  have hr := elementary_rank_le_of_embedding hA ψ hψ
  let : IsCyclic (MulAut.Outer L) := BinaryLinear.OuterCyclic.psl_outer_isCyclic hd
  let P : Sylow 2 (MulAut.Outer L) := Classical.choice inferInstance
  have hcyclic := P.primeRank_le_one_of_isCyclic inferInstance
  have hlow := finrank_le_fixedCodim_of_disjoint_translate ρ I b hdis
  have hm := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr hb))
  have hcodA := fixedCodim_add_finrank ρ A
  have hcodb := fixedCodim_add_finrank ρ (zpowers b)
  have hcod := hoff.2
  omega

/-- The source generation hypothesis eliminates the whole outer extension. -/
theorem whole_of_marked_outer_summands [Finite G]
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (φ : G →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)))
    (hφ : Function.Injective φ) (L : Subgroup G)
    (hmark : L.map φ = MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)))
    (I : Submodule (ZMod 2) V) (hdim : d ≤ Module.finrank (ZMod 2) I)
    (hstable : L ≤ subspaceStabilizer ρ I)
    (hfaith : ∀ g ∈ L, (∀ v ∈ I, ρ g v = v) → g = 1)
    (hswap : ∀ b ∉ L, Disjoint I (I.map (ρ b)))
    (hgenerated : offenderSubgroup ρ = ⊤) : L = ⊤ := by
  have hinner (g : G) (hi : φ g ∈ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2))) : g ∈ L := by
    rw [← hmark] at hi
    obtain ⟨l, hl, he⟩ := hi
    exact hφ he ▸ hl
  apply top_unique
  rw [← hgenerated]
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA, _⟩ b hb
  by_contra hbL
  have hout : φ b ∉ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) := fun hi => hbL (hinner b hi)
  exact not_offender_of_outer_disjoint_translate ρ hd φ hφ I hdim
    (fun g hg => hstable (hinner g hg)) (fun g hg => hfaith g (hinner g hg))
    hA.1 hb hout (hswap b hbL) (hA.isOffender ρ)

end CFSG.Quasithin.ChapterB.QuasisimpleSource
