module

public import Theory.Representation.SymplecticConjugatePair.Ambient
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.Setup
public import CFSG.Quasithin.ChapterE.Section04.Basic
public import Theory.Representation.SymplecticConjugatePair.Parabolics

/-!
# Acting-overgroup reductions for H.7

The actual source action embeds faithfully into the binary normalizer of its
derived paired matrix image: this uses normality of the solvable residual,
not normality of an arbitrary embedded subgroup. Twists are compared to the
canonical graph pair by actual binary linear equivalences.

If the actors permute the two summands, a member of E.3.8 with k>1 preserves
each summand. Its intersection with the index-two stabilizer fixes a nonzero
vector in the first summand, while any swapping actor would move that vector
to the disjoint summand. A swapping-involution centralizer bound similarly
excludes swapping (F−1)-offenders. Both the permutation assertion and that
centralizer bound remain explicit model obligations. Native residual bounds
are transported without treating Sp₄(2) as its derived subgroup.

Full-group root and parabolic witnesses are placed only in the explicitly
generated enlargement `standardAmbient`. No equality for every source Setup
is inferred from those witnesses. Table 7.2.1 asks for upper/lower bounds;
normalizer coverage and the standard overgroup's two-subgroup analysis are
still required to finish those bounds.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, standing setup
on printed p.377, H.7 on pp.388–389, and the paired-module setup and parameter
conventions on pp.696–698 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open SymplecticConjugatePair SymplecticConjugatePair.Ambient
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
variable {F M : Type*} [Field F] [Algebra (ZMod 2) F] [Group M]

lemma Setup.linear_restriction (D : Setup F M) :
    (linearAction D.action).comp D.embedding = linearAction (derivedPair D.twist) := by
  apply MonoidHom.ext
  intro x
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun ρ : Representation (ZMod 2) (commutator (Sp F)) (Space F) => ρ x v)
    D.restriction

lemma Setup.image_residual (D : Setup F M) :
    (Subgroup.solvableResidual M).map (linearAction D.action) = derivedImage D.twist := by
  rw [← D.range_eq_residual, MonoidHom.map_range, D.linear_restriction]
  rfl

noncomputable def Setup.normalizerHom (D : Setup F M) : M →* pairedNormalizer D.twist :=
  (linearAction D.action).codRestrict _ (fun g => by
    change linearAction D.action g ∈ Subgroup.normalizer (derivedImage D.twist)
    rw [← D.image_residual]
    apply Subgroup.le_normalizer_map (linearAction D.action)
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g)

lemma Setup.normalizerHom_injective (D : Setup F M) :
    Function.Injective D.normalizerHom := by
  intro g h he
  exact linearAction_injective D.action D.faithful (congrArg Subtype.val he)

@[simp] lemma Setup.normalizerHom_action (D : Setup F M) (g : M) (v : Space F) :
    normalizerAction D.twist (D.normalizerHom g) v = D.action g v := rfl

variable [Finite F]

lemma Setup.stabilizer_index_two (D : Setup F M) (hp : PermutesSummands D.action) :
    (summandStabilizer D.action).index = 2 :=
  summandStabilizer_index_two D.action hp D.interchange

/-- A member of any E.3.8 family with k > 1 preserves each summand.
The actual permutation of the two summands remains an explicit input. -/
lemma Setup.family_le_stabilizer (D : Setup F M) (hp : PermutesSummands D.action)
    {k : ℕ} (hk : 1 < k) {A : Subgroup M}
    (hA : A ∈ ChapterE.fixedSpaceFamily D.action k) : A ≤ summandStabilizer D.action := by
  let _ : IsElementaryAbelian 2 A := hA.2.1.2
  let N := summandStabilizer D.action
  have hn : N.index = 2 := D.stabilizer_index_two hp
  let _ : N.Normal := N.normal_of_index_eq_two hn
  let B := A ⊓ N
  have hi : B.relIndex A ≤ 2 := by
    have hdiv := N.relIndex_dvd_index_of_normal A
    rw [hn, ← Subgroup.inf_relIndex_left] at hdiv
    exact Nat.le_of_dvd (by decide) hdiv
  have hc : Nat.log 2 (B.relIndex A) < k := by
    have hlog := Nat.log_mono_right (b := 2) hi
    norm_num at hlog
    omega
  have heq := hA.2.2 B inf_le_left hc
  by_contra hAN
  obtain ⟨s, hsA, hsN⟩ := SetLike.not_le_iff_exists.mp hAN
  have hB : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (Subgroup.inclusion (show B ≤ A from inf_le_left)) (Subgroup.inclusion_injective _)
  exact fixedSpace_ne_of_swapping D.action hB (show B ≤ N from inf_le_right) hsA
    (swaps_of_not_mem_stabilizer D.action hp hsN) heq

lemma Setup.family_two_n_le_stabilizer (D : Setup F M)
    (hp : PermutesSummands D.action) {n : ℕ} (hn : 0 < n) {A : Subgroup M}
    (hA : A ∈ ChapterE.fixedSpaceFamily D.action (2*n)) :
    A ≤ summandStabilizer D.action := D.family_le_stabilizer hp (by omega) hA

variable [Finite M]

lemma Setup.offender_le_stabilizer (D : Setup F M)
    (hp : PermutesSummands D.action) {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (hc : ∀ s : M, orderOf s = 2 → SwapsSummands D.action s →
      primeRank 2 (Subgroup.centralizer ({s} : Set M)) ≤ n+1)
    {A : Subgroup M} (hA : IsElementaryTwo A)
    (hoff : fixedCodim D.action A ≤ rank A + 1) : A ≤ summandStabilizer D.action := by
  by_contra hAN
  obtain ⟨s, hsA, hsN⟩ := SetLike.not_le_iff_exists.mp hAN
  have hswap := swaps_of_not_mem_stabilizer D.action hp hsN
  have hne : s ≠ 1 := fun he => hsN (he ▸ (summandStabilizer D.action).one_mem)
  let _ : IsElementaryAbelian 2 A := hA.2
  have hs : orderOf s = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian s hsA) hne
  exact (not_offender_of_swapping D.action hF hn hA hsA hswap (hc s hs hswap)).not_ge hoff

variable [CharP F 2]

omit [Finite M] in
lemma Setup.residual_fixedCodim (D : Setup F M) (A : Subgroup (commutator (Sp F))) :
    fixedCodim D.action (A.map D.embedding) = fixedCodim (derivedPair graphAut) A := by
  have h := fixedSpace_comp_map D.action D.embedding A
  rw [D.restriction] at h
  change Module.finrank (ZMod 2) (Space F ⧸ fixedSpace D.action (A.map D.embedding)) = _
  rw [← h]
  exact derivedPair_fixedCodim_eq_graphPair D.twist D.movesDiagram A

omit [Finite M] in
/-- A native involution bound transfers to the actual embedded residual. -/
lemma Setup.residual_involution_bound (D : Setup F M) {n : ℕ}
    (hi : ∀ x : commutator (Sp F), orderOf x = 2 →
      3*n ≤ fixedCodim (derivedPair graphAut) (Subgroup.zpowers x))
    (s : M) (hs : s ∈ Subgroup.solvableResidual M) (ho : orderOf s = 2) :
    3*n ≤ fixedCodim D.action (Subgroup.zpowers s) := by
  rw [← D.range_eq_residual] at hs
  obtain ⟨x, rfl⟩ := hs
  rw [← MonoidHom.map_zpowers, D.residual_fixedCodim]
  apply hi
  rwa [← orderOf_injective D.embedding D.embedding_injective x]

omit [Finite M] in
/-- A native (F−1) exclusion transfers to each actual residual subgroup. -/
lemma Setup.residual_not_offender (D : Setup F M)
    (hi : ∀ B : Subgroup (commutator (Sp F)), IsElementaryTwo B →
      rank B + 1 < fixedCodim (derivedPair graphAut) B)
    {A : Subgroup M} (hA : IsElementaryTwo A)
    (hAL : A ≤ Subgroup.solvableResidual M) : rank A + 1 < fixedCodim D.action A := by
  let B := A.comap D.embedding
  have hbmap : B.map D.embedding = A := Subgroup.map_comap_eq_self
    (D.range_eq_residual ▸ hAL)
  have hbne : B ≠ ⊥ := by
    intro h
    apply hA.1
    rw [← hbmap, h, Subgroup.map_bot]
  let _ : IsElementaryAbelian 2 A := hA.2
  have hBe : IsElementaryAbelian 2 B := by
    refine { toIsMulCommutative := A.comap_injective_isMulCommutative D.embedding_injective
             exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply D.embedding_injective
    change D.embedding ((x : commutator (Sp F))^2) = D.embedding 1
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (D.embedding x.val) x.property
  have h := hi B ⟨hbne, hBe⟩
  rw [← D.residual_fixedCodim, hbmap] at h
  have hr := rank_map_injective D.embedding D.embedding_injective B
  rw [hbmap] at hr
  omega

/-- Full-group root witnesses live in the explicit enlargement; no containment
of that full group in an arbitrary source Setup is asserted. -/
theorem standard_root_witness {n : ℕ} (hF : Nat.card F = 2^n) (r : Fin 8) :
    orderOf (fullHom (rootElement r (1 : F))) = 2 ∧
      fixedCodim (standardAction (F := F))
        (Subgroup.zpowers (fullHom (rootElement r (1 : F)))) = 3*n := by
  constructor
  · rw [orderOf_injective fullHom fullHom_injective]
    exact root_involution r one_ne_zero
  · have h := fixedCodim_map_equivariant graphPair standardAction fullHom
      (LinearEquiv.refl (ZMod 2) (Space F)) (fun _ _ => rfl)
      (Subgroup.zpowers (rootElement r (1 : F)))
    rw [MonoidHom.map_zpowers] at h
    rw [← h]
    exact root_fixedCodim_of_card hF r one_ne_zero

/-- The rank-3n parabolic witness also lies in the explicit enlargement,
including at n=1 where its full symplectic carrier is not the source residual. -/
theorem standard_plane_witness {n : ℕ} (hF : Nat.card F = 2^n) :
    IsElementaryAbelian 2 ((planeRadical (F := F)).map fullHom) ∧
      rank ((planeRadical (F := F)).map fullHom) = 3*n ∧
      fixedCodim (standardAction (F := F)) ((planeRadical (F := F)).map fullHom) = 5*n := by
  let _ : IsElementaryAbelian 2 (planeRadical (F := F)) := planeRadical_elementary
  refine ⟨IsElementaryAbelian.map fullHom, ?_, ?_⟩
  · rw [rank_map_injective fullHom fullHom_injective, rank_planeRadical hF]
  · rw [← fixedCodim_map_equivariant graphPair standardAction fullHom
      (LinearEquiv.refl (ZMod 2) (Space F)) (fun _ _ => rfl)]
    exact planeRadical_fixedCodim hF

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
