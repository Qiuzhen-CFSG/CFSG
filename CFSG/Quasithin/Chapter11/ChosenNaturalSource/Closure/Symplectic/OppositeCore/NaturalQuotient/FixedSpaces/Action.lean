module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Factors
public import Theory.Representation.ElementaryPerfectSplit
/-!
# Fixed factors in the original opposite-core quotient

The Frattini bounds make W and Wʸ fix their respective factors in
Q/N, where N=(W∩Wʸ)V. The factors are complementary. An I-conjugator
exchanging them forces the global fixed subgroup to be trivial: a fixed
element in one factor also lies in the other. Decomposing a fixed element
then identifies the fixed subgroup of each whole root with its literal
factor. Every step uses the original quotient projection and conjugation.

The inner conjugator is constructed in FixedSpaces/Conjugator.lean and
applied in the parent module. Descent to SL₂ and fixed spaces for individual
nonidentity root elements are separate subsequent steps.
Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
set_option backward.isDefEq.respectTransparency false
public noncomputable section
private theorem fixed_generators {H M : Type*} [Group H] [Group M]
    (ρ : H →* MulAut M) (U Z : Subgroup H) (hgen : U ⊔ Z = ⊤)
    (v : M) (hU : ∀ u ∈ U, ρ u v = v) (hZ : ∀ z ∈ Z, ρ z v = v) :
    ∀ h, ρ h v = v := by
  let S : Subgroup H := {
    carrier := {h | ρ h v = v}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change ρ (a*b) v = v
      rw [map_mul]
      change ρ a (ρ b v) = v
      rw [show ρ b v = v from hb]
      exact ha
    inv_mem' := by
      intro a ha
      change (ρ a⁻¹) v = v
      rw [map_inv]
      exact (ρ a).symm_apply_eq.mpr ha.symm }
  have hs : U ⊔ Z ≤ S := sup_le hU hZ
  intro h
  exact hs (hgen ▸ mem_top h)

private theorem fixed_of_complementary_conjugate_factors
    {H M : Type*} [Group H] [CommGroup M]
    (ρ : H →* MulAut M) (U Z : Subgroup H) (hgen : U ⊔ Z = ⊤)
    (A B : Subgroup M) (hAB : IsCompl A B)
    (hA : ∀ u ∈ U, ∀ a ∈ A, ρ u a = a)
    (hB : ∀ z ∈ Z, ∀ b ∈ B, ρ z b = b)
    (i : H) (hi : A.map (ρ i).toMonoidHom = B) :
    (∀ v, (∀ h, ρ h v = v) → v = 1) ∧
    (∀ v, (∀ u ∈ U, ρ u v = v) ↔ v ∈ A) ∧
    (∀ v, (∀ z ∈ Z, ρ z v = v) ↔ v ∈ B) := by
  have hzeroA (a : M) (ha : a ∈ A) (hf : ∀ h, ρ h a = a) : a = 1 := by
    have hb : a ∈ B := by
      rw [← hi, ← hf i]
      exact mem_map_of_mem _ ha
    exact mem_bot.mp (hAB.disjoint.le_bot ⟨ha,hb⟩)
  have hzeroB (b : M) (hb : b ∈ B) (hf : ∀ h, ρ h b = b) : b = 1 := by
    obtain ⟨a,ha,he⟩ := hi.symm ▸ hb
    have haeq : a = b := (ρ i).injective (he.trans (hf i).symm)
    exact hzeroA b (haeq ▸ ha) hf
  have hdecomp (v : M) : ∃ a ∈ A, ∃ b ∈ B, a*b=v := by
    exact mem_sup_of_normal_left.mp (hAB.sup_eq_top ▸ mem_top v)
  have hfixU (v : M) (hf : ∀ u ∈ U, ρ u v = v) : v ∈ A := by
    obtain ⟨a,ha,b,hb,rfl⟩ := hdecomp v
    have hbU : ∀ u ∈ U, ρ u b = b := by
      intro u hu
      have hh := hf u hu
      rw [map_mul,hA u hu a ha] at hh
      exact mul_left_cancel hh
    rw [hzeroB b hb (fixed_generators ρ U Z hgen b hbU (fun z hz => hB z hz b hb)),mul_one]
    exact ha
  have hfixZ (v : M) (hf : ∀ z ∈ Z, ρ z v = v) : v ∈ B := by
    obtain ⟨a,ha,b,hb,rfl⟩ := hdecomp v
    have haZ : ∀ z ∈ Z, ρ z a = a := by
      intro z hz
      have hh := hf z hz
      rw [map_mul,hB z hz b hb] at hh
      exact mul_right_cancel hh
    rw [hzeroA a ha (fixed_generators ρ U Z hgen a (fun u hu => hA u hu a ha) haZ),one_mul]
    exact hb
  exact ⟨fun v hv => hzeroA v (hfixU v (fun u _ => hv u)) hv,
    fun v => ⟨hfixU v,fun hv u hu => hA u hu v hv⟩,
    fun v => ⟨hfixZ v,fun hv z hz => hB z hz v hv⟩⟩

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

private theorem factor_fixed {G : Type*} [Group G]
    (I Q N H A : Subgroup G) [(N.subgroupOf Q).Normal]
    (hIQ : I ≤ normalizer (Q : Set G))
    (hcomm : ⁅H,A⁆ ≤ N)
    (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q))
    (hρ : ∀ i : I, ∀ q : Q, ∀ hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q,
      ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
        QuotientGroup.mk' (N.subgroupOf Q) ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩)
    (i : I) (hi : (i:G) ∈ H) (v : Q ⧸ N.subgroupOf Q)
    (hv : v ∈ ((A ⊓ Q).subgroupOf Q).map (QuotientGroup.mk' (N.subgroupOf Q))) :
    ρ i v = v := by
  obtain ⟨q,hq,rfl⟩ := hv
  rw [hρ i q (le_normalizer_iff.mp hIQ i i.property q q.property)]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (i:G)*(q:G)*(i:G)⁻¹ / (q:G) ∈ N
  simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using
    hcomm (commutator_mem_commutator hi hq.1)

private theorem quotient_factor_conjugate {G : Type*} [Group G]
    (I Q N A B : Subgroup G) [(N.subgroupOf Q).Normal]
    (hIQ : I ≤ normalizer (Q : Set G))
    (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q))
    (hρ : ∀ i : I, ∀ q : Q, ∀ hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q,
      ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
        QuotientGroup.mk' (N.subgroupOf Q) ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩)
    (i : I) (hi : A.map (MulAut.conj (i:G)).toMonoidHom = B) :
    ((((A ⊓ Q).subgroupOf Q).map (QuotientGroup.mk' (N.subgroupOf Q))).map
      (ρ i).toMonoidHom) =
      ((B ⊓ Q).subgroupOf Q).map (QuotientGroup.mk' (N.subgroupOf Q)) := by
  apply le_antisymm
  · rintro v ⟨u,⟨q,hq,rfl⟩,rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hρ i q (le_normalizer_iff.mp hIQ i i.property q q.property)]
    apply mem_map_of_mem
    exact ⟨hi ▸ mem_map_of_mem (MulAut.conj (i:G)).toMonoidHom hq.1,
      le_normalizer_iff.mp hIQ i i.property q q.property⟩
  · rintro v ⟨q,hq,rfl⟩
    have hqQ : (i:G)⁻¹*(q:G)*(i:G) ∈ Q := by
      simpa only [coe_inv,inv_inv] using le_normalizer_iff.mp hIQ i⁻¹ i⁻¹.property q q.property
    have hqA : (i:G)⁻¹*(q:G)*(i:G) ∈ A := by
      obtain ⟨a,ha,he⟩ := hi.symm ▸ hq.1
      change (i:G)*a*(i:G)⁻¹=(q:G) at he
      have he' : (i:G)⁻¹*(q:G)*(i:G) = a := by
        rw [← he]
        simp [mul_assoc]
      exact he' ▸ ha
    let q' : Q := ⟨(i:G)⁻¹*(q:G)*(i:G),hqQ⟩
    refine ⟨QuotientGroup.mk' (N.subgroupOf Q) q',mem_map_of_mem _ ⟨hqA,hqQ⟩,?_⟩
    change ρ i (QuotientGroup.mk' (N.subgroupOf Q) q') = _
    rw [hρ i q' (le_normalizer_iff.mp hIQ i i.property q' q'.property)]
    congr 1
    apply Subtype.ext
    change (i:G)*((i:G)⁻¹*(q:G)*(i:G))*(i:G)⁻¹=(q:G)
    group

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The first root acts trivially on the first literal quotient factor. -/
theorem root_fixes_first_factor (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2) :
    let I := oppositeJoin (auxiliaryW E) y
    let Q := corePair (auxiliaryW E) y
    let N := pairDenominator E y
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    ∀ (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q))
      (_hρ : ∀ i : I, ∀ q : Q, ∀ hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q,
        ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
          QuotientGroup.mk' (N.subgroupOf Q) ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩)
      (i : I), (i:G) ∈ auxiliaryW E → ∀ v,
      v ∈ (((auxiliaryW E ⊔ V) ⊓ Q).subgroupOf Q).map (QuotientGroup.mk' (N.subgroupOf Q)) →
      ρ i v = v := by
  dsimp only
  intro ρ hρ i hi v hv
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  have hp := source_corePair_properties E m hy hcore
  have hn := (normal_subgroupOf_iff_le_normalizer (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  apply factor_fixed _ _ _ (auxiliaryW E) (auxiliaryW E ⊔ V) hn _ ρ hρ i hi v hv
  have hWV := (le_sup_left : auxiliaryW E ≤ oppositeJoin (auxiliaryW E) y).trans
    (oppositeJoin_normalizes_seed E m hy hW)
  have hd := (derived_le_of_frattini_image_le
    ((isPGroup_pCoreIn 2 E.G₁).to_le ((auxiliaryW_le_W E).trans hW)) hPhi).trans E.V₁_le
  rw [commutator_comm]
  apply le_trans (commutator_sup_le_of_relative_normal
    (auxiliaryW E ⊔ V) (auxiliaryW E) V (auxiliaryW E) V
    (sup_le hWV V.le_normalizer) le_sup_left le_sup_right hd
      (le_normalizer_iff_commutator_le_left.mp hWV)) le_sup_right

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

private theorem commutator_factor_le {G : Type*} [Group G] (W V : Subgroup G)
    (hn : W ≤ normalizer (V : Set G)) (hd : ⁅W,W⁆ ≤ V) : ⁅W,W ⊔ V⁆ ≤ V := by
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (W ⊔ V) W V W V
    (sup_le hn V.le_normalizer) le_sup_left le_sup_right hd
      (le_normalizer_iff_commutator_le_left.mp hn)

/-- Both whole-root fixed spaces are the literal complementary factors.
The conjugator premise is supplied from the marked geometry below. -/
theorem quotient_fixed_factors_of_inner_conjugator (m : MarkedFlag E)
    {y : G} (hy : y ∈ L) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2)
    (i : oppositeJoin (auxiliaryW E) y)
    (hi : (auxiliaryW E).map (MulAut.conj (i:G)).toMonoidHom =
      (auxiliaryW E).map (MulAut.conj y).toMonoidHom) :
    let I := oppositeJoin (auxiliaryW E) y
    let Q := corePair (auxiliaryW E) y
    let N := pairDenominator E y
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    ∀ (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q))
      (_hρ : ∀ i : I, ∀ q : Q, ∀ hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q,
        ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
          QuotientGroup.mk' (N.subgroupOf Q) ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩),
      (∀ v, (∀ j : I, ρ j v = v) → v = 1) ∧
      (∀ v, (∀ j : I, (j:G) ∈ auxiliaryW E → ρ j v = v) ↔
        v ∈ (((auxiliaryW E ⊔ V) ⊓ Q).subgroupOf Q).map (QuotientGroup.mk' (N.subgroupOf Q))) ∧
      (∀ v, (∀ j : I, (j:G) ∈ (auxiliaryW E).map (MulAut.conj y).toMonoidHom → ρ j v = v) ↔
        v ∈ ((((auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊔ V) ⊓ Q).subgroupOf Q).map
          (QuotientGroup.mk' (N.subgroupOf Q))) := by
  dsimp only
  intro ρ hρ
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  let _ := quotient_elementary E m hy hW hPhi hcore
  let W := auxiliaryW E
  let Z := W.map (MulAut.conj y).toMonoidHom
  let I := oppositeJoin W y
  let Q := corePair W y
  let N := pairDenominator E y
  have hp := source_corePair_properties E m hy hcore
  have hIQ := (normal_subgroupOf_iff_le_normalizer (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  have hgen : W.subgroupOf I ⊔ Z.subgroupOf I = ⊤ := by
    rw [← subgroupOf_sup (show W ≤ I from le_sup_left) (show Z ≤ I from le_sup_right)]
    exact subgroupOf_self I
  have hdW : ⁅W,W⁆ ≤ V := (derived_le_of_frattini_image_le
    ((isPGroup_pCoreIn 2 E.G₁).to_le ((auxiliaryW_le_W E).trans hW)) hPhi).trans E.V₁_le
  have hIV := oppositeJoin_normalizes_seed E m hy hW
  have hdZ : ⁅Z,Z⁆ ≤ V := by
    rw [← map_commutator]
    exact (map_mono hdW).trans (mem_normalizer_iff_map_conj_eq.mp (D.normalizes hy)).le
  have hab : (W ⊔ V).map (MulAut.conj (i:G)).toMonoidHom = Z ⊔ V := by
    have hv := mem_normalizer_iff_map_conj_eq.mp (hIV i.property)
    change V.map (MulAut.conj (i:G)).toMonoidHom = V at hv
    rw [Subgroup.map_sup,hi,hv]
  exact fixed_of_complementary_conjugate_factors ρ (W.subgroupOf I) (Z.subgroupOf I) hgen _ _
    (quotient_factors_complementary E m hy hW hPhi hsplit)
    (fun j hj v hv => root_fixes_first_factor E m hy hW hPhi hcore ρ hρ j hj v hv)
    (fun j hj v hv => factor_fixed I Q N Z (Z ⊔ V) hIQ
      ((commutator_factor_le Z V (le_sup_right.trans hIV) hdZ).trans le_sup_right)
      ρ hρ j hj v hv)
    i (quotient_factor_conjugate I Q N (W ⊔ V) (Z ⊔ V) hIQ ρ hρ i hab)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
