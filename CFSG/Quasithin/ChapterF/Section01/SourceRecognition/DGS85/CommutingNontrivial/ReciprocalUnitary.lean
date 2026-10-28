module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryActorDegree

/-!
# Unitary field-square estimates on original moving centers

An elementary actor of order at least four in SU₃ is carried into a standard
central root by a Hermitian basis change and Sylow conjugation. The proved
three-conjugate root bound then gives displacement index at least q² for
any nontrivial binary action. An elementary lift through the odd scalar
kernel gives the same statement for PSU₃, with its order and fixed space
unchanged. No faithfulness of the full special unitary action is asserted.

The source application constructs the original conjugation action on Z_lambda,
proves it nontrivial from the earlier residual fixed-space calculation, and
identifies the actor order and fixed-space index with the original subgroup
indices. `ReciprocalUnitaryIntersection` applies this to Z_alpha intersect
Q_alpha'. The actor of order two remains a separate case of 5.10(b).

Source: DGS, *Groups and Graphs* (1985), (5.10)(b), pp.110--112, and
(8.2)(**), pp.134--135. This covers the unitary actors of order at least four;
it does not assert the whole reciprocal-escape theorem or later conclusions.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open Representation.SU3.CubicDegree.InnerActors
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private theorem map_equiv_inverse {D E : Type*} [Group D] [Group E]
    (A : Subgroup D) (e : D ≃* E) :
    (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [map_map]
  rw [show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D from by
    ext x
    exact e.symm_apply_apply x, map_id]

private theorem special_elementary_field_square_bound
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup J.specialSubgroup) [IsElementaryAbelian 2 A] (hAc : 4 ≤ Nat.card A) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  let : CharP K 2 := charTwo_of_card hK
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  let J₀ := standardForm J
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hfixed
  let e := specialEquiv J C hC
  let A₀ := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A₀).exists_le_sylow
  have hAZ : A₀ ≤ sylowCenter P := by
    rw [sylowCenter,←(HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl P).1]
    rw [←omegaOneAmbient_eq_self A₀]
    exact omegaOneAmbient_mono hAP
  obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J₀ rfl hn hK hfixed
  have hcentralcard : Nat.card (central J₀ rfl) = 2^n := by
    let f := (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl).comp
      (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J₀)
    have hu : Function.Injective (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl) := by
      intro z w he
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 1) he)
        (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 2) he)
    have hf : Function.Injective f := hu.comp
      (HermitianForm.BorelTorus.EvenCenterAction.centralCoord_injective J₀)
    change Nat.card f.range = 2^n
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    exact hfixed
  have hRcard : Nat.card (sylowCenter R) = 2^n := by
    rw [sylowCenter,←(HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R).1]
    exact (HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R).2.2
  have hReq : sylowCenter R = central J₀ rfl :=
    (eq_of_le_of_card_ge hR (hRcard.trans hcentralcard.symm).le).symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J₀.specialSubgroup P R
  let f := e.trans (MulAut.conj g)
  have hAf : A.map f.toMonoidHom ≤ central J₀ rfl := by
    have hz : (sylowCenter P).map (MulAut.conj g).toMonoidHom = sylowCenter R := by
      rw [sylowCenter,map_embeddedCenter _ _ (MulAut.conj g).injective]
      exact congrArg (fun T : Subgroup J₀.specialSubgroup => (center T).map T.subtype)
        (congrArg Sylow.toSubgroup hg)
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,←map_map]
    exact (map_mono hAZ).trans_eq (hz.trans hReq)
  let σ := ρ.comp f.symm.toMonoidHom
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    refine ⟨f x,?_⟩
    change ρ (f.symm (f x)) ≠ 1
    simpa only [f.symm_apply_apply] using hx
  have hb := su3_root_actor_field_index J₀ rfl hn hK hconj σ hσ
    (A.map f.toMonoidHom) hAf (by rwa [card_map_of_injective f.injective])
  rw [fixedSpace_comp_map,map_equiv_inverse] at hb
  simpa only [←pow_mul,Nat.mul_comm n 2] using hb

private theorem projective_elementary_field_square_bound
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W)
    (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    [IsElementaryAbelian 2 A] (hAc : 4 ≤ Nat.card A) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  let σ := ρ.comp J.specialToProjective
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    obtain ⟨y,rfl⟩ := J.specialToProjective_surjective x
    exact ⟨y,hx⟩
  obtain ⟨D,hD,hDA,hDc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    J.specialToProjective J.specialToProjective_surjective
    (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker) A
  let : IsElementaryAbelian 2 D := hD
  have hb := special_elementary_field_square_bound J hn hK hconj σ hσ D (hDc.symm ▸ hAc)
  rwa [fixedSpace_comp_map,hDA] at hb


open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem moving_elementary_field_square_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D)
    (c : ℕ)
    (hbound : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W],
      ∀ (ρ : Representation (ZMod 2) D W), (∃ g, ρ g ≠ 1) →
        ∀ A : Subgroup D, IsElementaryAbelian 2 A → 4 ≤ Nat.card A →
          c^2 ≤ Nat.card (W ⧸ fixedSpace ρ A))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup w.val)
    (hAc : 4 ≤ (Q (family P) w.val).relIndex A) :
    c^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let F := family P
  let L := d.localGroup w.val
  let Z₀ := Z F w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  obtain ⟨ρ,S,hact,_,_,_,_,hres,_⟩ := source_moving_center_module h d hc hab hd hb hcomm w hm e
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hiA := BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F w.val)
    A q (local_quotient_kernel F d w.val e) hAL
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! ht
    have he : fixedSpace ρ (pResidual 2 D) = ⊤ := by
      apply top_unique
      intro z _ g
      change ρ g z = z
      rw [ht]
      rfl
    exact top_ne_bot (he.symm.trans hres)
  have hlo := hbound (Additive Z₀) ρ hnt ((A.subgroupOf L).map q) inferInstance
    (hiA.symm ▸ hAc)
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  have hi := center_action_fixed_index L Z₀ A hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) hAL q ρ hact
  rwa [hi] at hlo

/-- The unitary field-square estimate for every elementary original actor
whose quotient image has at least four elements. The action is the literal
conjugation on the moving center; no faithfulness or field marking is assumed
beyond the displayed actual quotient equivalence. -/
theorem source_moving_special_unitary_field_square_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* J.specialSubgroup)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup w.val)
    (hAc : 4 ≤ (Q (family P) w.val).relIndex A) :
    (2^n)^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply moving_elementary_field_square_bound h d hc hab hd hb hcomm w hm e (2^n) ?_ A hAL hAc
  intro W _ _ _ ρ hnt C hC hcC
  let : IsElementaryAbelian 2 C := hC
  exact special_elementary_field_square_bound J hn hK hconj ρ hnt C hcC

/-- The unitary field-square estimate for every elementary original actor
whose quotient image has at least four elements. The action is the literal
conjugation on the moving center; no faithfulness or field marking is assumed
beyond the displayed actual quotient equivalence. -/
theorem source_moving_projective_unitary_field_square_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup w.val)
    (hAc : 4 ≤ (Q (family P) w.val).relIndex A) :
    (2^n)^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply moving_elementary_field_square_bound h d hc hab hd hb hcomm w hm e (2^n) ?_ A hAL hAc
  intro W _ _ _ ρ hnt C hC hcC
  let : IsElementaryAbelian 2 C := hC
  exact projective_elementary_field_square_bound J hn hK hconj ρ hnt C hcC

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
