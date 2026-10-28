module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.Conjugation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedFacts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.CubicModules
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.FixedLineCompatibility

/-!
# The root and the two literal even fusion four-groups

The nonzero vector b fixed by u in [A(z),X] has a square root v*u,
where v is a cubic conjugate of b. We choose w = v*u*z. The moved four
is exactly the even part of A(z), so this choice gives the literal marked
identity A(z) ∩ A₆ = ⟨b,uwz⟩ without changing w² = b.

Core reciprocity and the fixed-vector calculation identify t = zb with
the selected source conjugate and place z and u in Q_t. Their fusion
then supplies ⟨b,uz⟩ inside the second even group. The order-eight bound
and the odd element z prove equality. Both choices u = a.u and u = a.u*z
are covered by the commuting-cubic adapter.

The earlier-source assertion that square roots of z lie in Q_z remains
explicit. Its existing producer is the SquareRoots module under
LocalGluing.FixedLineCompatibility. The permutation cycle type and the
centralizer generation are separate from these group calculations.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 2.3(1), 4.6 and 4.8, pp.33–34 and 40–41.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- Forget only the already constructed symmetric subgroup and its marking. -/
def SymmetricSixData.commutingCubicData (s : SymmetricSixData h a) :
    CommutingCubicData h a where
  u := s.u
  u_choice := s.u_choice
  u_order := s.u_order
  u_fused := s.u_fused
  X1 := s.X1
  card_X1 := s.card_X1
  X1_centralizes_X := s.X1_centralizes_X
  z_inverts_X1 := s.z_inverts_X1
  u_centralizes_X1 := s.u_centralizes_X1
  centralizer_X_card := s.centralizer_X_card

namespace QuaternionExchange
open LocalGluing
variable {s : SymmetricSixData h a}

private theorem core_reciprocity_base (h : Hypotheses z) {r : G} (hr : IsConj z r)
    (hm : r ∈ coreInG z) : z ∈ coreInG r := by
  by_cases he : r = z
  · exact he ▸ h.involution_mem_coreInG
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  have hi := (NonnormalRecognition.involution_mem_coreIntersection h g hm he).2
  rwa [map_coreInG] at hi

private theorem core_reciprocity (h : Hypotheses z) {r q : G} (hr : IsConj z r)
    (hq : IsConj z q) (hm : q ∈ coreInG r) : r ∈ coreInG q := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  let e : G ≃* G := MulAut.conj g
  have hm' : e.symm q ∈ coreInG z := by
    have hm0 : q ∈ (coreInG z).map e.toMonoidHom := (map_coreInG e z).symm ▸ hm
    exact mem_map_equiv.mp hm0
  have hz' : IsConj z (e.symm z) := isConj_iff.mpr ⟨g⁻¹, by simp [e]⟩
  have hq' : IsConj z (e.symm q) := hz'.trans (e.symm.toMonoidHom.map_isConj hq)
  have hb := core_reciprocity_base h hq' hm'
  have hh := mem_map_of_mem e.toMonoidHom hb
  simpa only [map_coreInG, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    e, MulAut.conj_apply] using hh

omit [Finite G] in
private theorem fusion_commute (d : FusionEightData z) {v w : G}
    (hv : v ∈ fusionCore z) (hw : w ∈ fusionCore z) : Commute v w := by
  let := d.elementary
  exact congrArg Subtype.val (mul_comm (⟨v,hv⟩ : fusionCore z) ⟨w,hw⟩)

omit [Finite G] in
private theorem square (d : FusionEightData z) {v : G}
    (hv : v ∈ fusionCore z) : v^2=1 := by
  let := d.elementary
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv

private theorem base_not_moved (k : CubicEightContext z s.u (cubicInG h))
    (p : CubicFourData z s.u (cubicInG h)) : z ∉ movedFour z (cubicInG h) := by
  intro hz
  have hzC : z ∈ centralizer (cubicInG h : Set G) :=
    (show z ∈ fusionCore z ⊓ centralizer (cubicInG h : Set G) from
      k.cubic_fixed.symm ▸ mem_zpowers z).2
  have hz1 : z=1 := show z ∈ (⊥ : Subgroup G) from p.fixed_free ▸ ⟨hz,hzC⟩
  have ho := h.involution
  simp [hz1] at ho

open scoped commutatorElement in
/-- Commutators of the two source subgroups have positive marked sign. -/
theorem movedFour_le_markedAlternating (s : SymmetricSixData h a) :
    movedFour z (cubicInG h) ≤ s.markedAlternating := by
  apply commutator_le.mpr
  intro v hv x hx
  have hvS := s.fusionCore_le_S hv
  have hxS : x ∈ s.S := by
    rw [s.generated]
    exact mem_sup_left (mem_sup_right hx)
  have hcS : ⁅v,x⁆ ∈ s.S := commutator_mem_commutator hvS hxS |>
    commutator_le_self s.S
  apply (s.mem_markedAlternating_iff _ hcS).mpr
  rw [Equiv.Perm.mem_alternatingGroup]
  let f : s.S →* ℤˣ := Equiv.Perm.sign.comp s.equiv.toMonoidHom
  change f ⟨⁅v,x⁆,hcS⟩ = 1
  have he : (⟨⁅v,x⁆,hcS⟩ : s.S) = ⁅(⟨v,hvS⟩ : s.S),⟨x,hxS⟩⁆ := rfl
  rw [he, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

/-- The source moved four is the entire even part of the first fusion eight. -/
theorem evenFusion_z_eq_movedFour (s : SymmetricSixData h a) (d : FusionEightData z) :
    s.evenFusion z = movedFour z (cubicInG h) := by
  have p := (cubicFourData_pair h d s.commutingCubicData).1
  apply (eq_of_le_of_card_ge (le_inf p.moved_le (movedFour_le_markedAlternating s)) ?_).symm
  change Nat.card (s.evenFusion z) ≤ Nat.card (movedFour z (cubicInG h))
  rw [s.evenFusion_z_card d, p.card]

omit [Finite G] in
private theorem sup_zpowers_eq_closure_pair (v w : G) :
    zpowers v ⊔ zpowers w = closure ({v,w} : Set G) := by
  apply le_antisymm
  · exact sup_le (zpowers_le.mpr (subset_closure (by simp)))
      (zpowers_le.mpr (subset_closure (by simp)))
  · apply (closure_le _).mpr
    rintro x (rfl | rfl)
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)

/-- Construct the root at the selected nonzero fixed vector, with its literal
first even-four marking. Square-root containment is the only extra premise. -/
theorem root_and_even_z_of_square_roots
    (d : FusionEightData z) (roots : ∀ v : G, v^2=z → v ∈ coreInG z)
    (s : SymmetricSixData h a) (b : G)
    (hb : b ∈ fixedLine z s.u (cubicInG h)) (hb1 : b ≠ 1) :
    ∃ r : RootData s, r.b = b ∧
      s.evenFusion z = zpowers r.b ⊔ zpowers (s.u*r.w*z) := by
  let c := s.commutingCubicData
  have k := (cubicEightContexts h d c).1
  have p := (cubicFourData_pair h d c).1
  have hbF := p.moved_le hb.1
  have hbf := d.fusion b hbF hb1
  have R := conjugateSquareRootsInCore_of_base roots
  have hz2 : z*z=1 := by simpa only [pow_two,h.involution] using pow_orderOf_eq_one z
  have hu2 : s.u*s.u=1 := by simpa only [pow_two,s.u_order] using pow_orderOf_eq_one s.u
  have hui : s.u⁻¹=s.u := inv_eq_iff_mul_eq_one.mpr hu2
  have hzi : z⁻¹=z := inv_eq_iff_mul_eq_one.mpr hz2
  have hzu : Commute z s.u := c.u_commutes_z.symm
  have hzb : z ≠ b := fun he => base_not_moved k p (he ▸ hb.1)
  have hzQ := core_reciprocity_base h hbf (fusionCore_le z hbF)
  have huQ : s.u ∉ coreInG b := by
    intro hu
    exact fixed_vector_not_other_core h d R (IsConj.refl z) s.u_fused k p hb hb1
      (core_reciprocity h hbf s.u_fused hu)
  obtain ⟨v,hbv,hv,hroot⟩ := fixed_vector_square_root k p hb
  change (v*s.u)^2=b at hroot
  have hvF := p.moved_le hv
  have hv2 := p.square hv
  have hvi : v⁻¹=v := inv_eq_iff_mul_eq_one.mpr hv2
  have hzv : Commute z v := (p.commutes_base hv).symm
  let w := (v*s.u)*z
  have hzw : Commute z w := (hzv.mul_right hzu).mul_right (Commute.refl z)
  have hw2 : w^2=b := by
    dsimp only [w]
    rw [((hzv.mul_right hzu).symm).mul_pow, hroot]
    simp only [pow_two, hz2, mul_one]
  have hwinv : s.u*w*s.u⁻¹=w⁻¹ := by
    have huz : s.u*z*s.u=z := by
      calc
        _ = z*(s.u*s.u) := by rw [← hzu.eq]; group
        _ = z := by rw [hu2,mul_one]
    dsimp only [w]
    rw [mul_inv_rev, mul_inv_rev, hzi, hui, hvi]
    calc
      _ = (s.u*v)*(s.u*z*s.u) := by group
      _ = s.u*v*z := by rw [huz]
      _ = z*(s.u*v) := ((hzu.mul_right hzv).eq).symm
  have hwmem : w ∈ fusionCore z ⊔ zpowers s.u := by
    exact (fusionCore z ⊔ zpowers s.u).mul_mem
      ((fusionCore z ⊔ zpowers s.u).mul_mem (mem_sup_left hvF)
        (mem_sup_right (mem_zpowers s.u))) (mem_sup_left h.involution_mem_fusionCore)
  let r : RootData s := {
    b := b, b_mem := hbF, b_ne_one := hb1, w := w, w_sq := hw2,
    w_mem := hwmem, w_mem_core := R b hbf w hw2, z_mem_core := hzQ,
    z_ne_b := hzb, u_not_core := huQ, z_commutes_w := hzw, u_inverts_w := hwinv }
  refine ⟨r,rfl,?_⟩
  change s.evenFusion z = zpowers b ⊔ zpowers (s.u*w*z)
  rw [evenFusion_z_eq_movedFour s d]
  have he : s.u*w*z = s.u*v*s.u⁻¹ := by
    simp only [w, hui, mul_assoc, hz2, mul_one]
  rw [he]
  have hvb : s.u*v*s.u⁻¹ = v*b := by
    apply mul_left_cancel (a := v)
    calc
      _ = (v*s.u)^2 := by rw [hui,pow_two]; group
      _ = b := hroot
      _ = v*(v*b) := by rw [← mul_assoc,hv2,one_mul]
  rw [hvb]
  have hv1 : v ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := isConj_iff.mp hbv
    exact hb1 ((MulAut.conj g).map_eq_one_iff.mp (hg.trans he))
  have hbvne : b ≠ v := by
    intro he
    have hbcomm : Commute b s.u := mem_centralizer_singleton_iff.mp hb.2
    have hs : (v*s.u)^2=1 := by
      rw [← he, hbcomm.mul_pow, square d hbF, pow_two,hu2,one_mul]
    exact hb1 (hroot.symm.trans hs)
  have hpair := isKleinFour_closure_pair b v (p.square hb.1) hv2 hb1 hv1 hbvne
    (fusion_commute d hbF hvF)
  have hgen : zpowers b ⊔ zpowers v = movedFour z (cubicInG h) := by
    apply eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hb.1) (zpowers_le.mpr hv))
    rw [sup_zpowers_eq_closure_pair, hpair.card_four, p.card]
  rw [← hgen]
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have hh := (zpowers b ⊔ zpowers (v*b)).mul_mem
      (mem_sup_right (mem_zpowers (v*b)))
      ((zpowers b ⊔ zpowers (v*b)).inv_mem (mem_sup_left (mem_zpowers b)))
    simpa only [mul_inv_cancel_right] using hh
  · exact sup_le le_sup_left (zpowers_le.mpr
      ((zpowers b ⊔ zpowers v).mul_mem (mem_sup_right (mem_zpowers v))
        (mem_sup_left (mem_zpowers b))))

omit [Finite G] in
private theorem fusion_data_of_conj (d : FusionEightData z) {r : G}
    (hr : IsConj z r) : FusionEightData r := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp hr
  exact fusionEightData_map (MulAut.conj g) d

private theorem evenFusion_card_le_four (s : SymmetricSixData h a)
    {t : G} (dt : FusionEightData t) (hzA : z ∈ fusionCore t) :
    Nat.card (s.evenFusion t) ≤ 4 := by
  classical
  have hi : s.evenFusion t ⊓ zpowers z = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxZ : x ∈ zpowers z := hx.2
    rw [mem_zpowers_iff_mem_range_orderOf,h.involution] at hxZ
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hxZ
    have hnlt := Finset.mem_range.mp hn
    interval_cases n
    · simp
    · exact (s.z_not_mem_markedAlternating (by simpa using hx.1.2)).elim
  have hn : zpowers z ≤ normalizer (s.evenFusion t : Set G) := by
    apply (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    intro y hy
    exact (fusion_commute dt hy.1 hzA).eq
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (s.evenFusion t) (zpowers z) hn
  rw [hi,card_bot,one_mul,Nat.card_zpowers,h.involution] at hc
  have hle : s.evenFusion t ⊔ zpowers z ≤ fusionCore t :=
    sup_le inf_le_left (zpowers_le.mpr hzA)
  have hb := card_le_of_le hle
  rw [dt.card, ← hc] at hb
  omega

/-- The second literal even fusion group, obtained from core reciprocity
and the selected source conjugate rather than a relabeling of the first. -/
theorem evenFusion_pivot_eq_of_square_roots
    (d : FusionEightData z) (roots : ∀ v : G, v^2=z → v ∈ coreInG z)
    (s : SymmetricSixData h a) (b : G)
    (hb : b ∈ fixedLine z s.u (cubicInG h)) (hb1 : b ≠ 1) :
    s.evenFusion (z*b) = zpowers b ⊔ zpowers (s.u*z) := by
  let c := s.commutingCubicData
  obtain ⟨p,p1⟩ := cubicFourData_pair h d c
  have k := (cubicEightContexts h d c).1
  have hbF := p.moved_le hb.1
  have hbf := d.fusion b hbF hb1
  have hz2 : z*z=1 := by simpa only [pow_two,h.involution] using pow_orderOf_eq_one z
  have hu2 : s.u*s.u=1 := by simpa only [pow_two,s.u_order] using pow_orderOf_eq_one s.u
  have hb2 := p.square hb.1
  have hzb : z ≠ b := fun he => base_not_moved k p (he ▸ hb.1)
  have ht1 : z*b ≠ 1 := by
    intro he
    apply hzb
    exact mul_right_cancel (he.trans hb2.symm)
  have htA : z*b ∈ fusionCore z := (fusionCore z).mul_mem h.involution_mem_fusionCore hbF
  have htf := d.fusion (z*b) htA ht1
  have dt := fusion_data_of_conj d htf
  have geom := selected_fixed_vector_geometry_of_square_roots h d roots c p p1 b hb hb1
  have he : z*b=a.g*z*a.g⁻¹ := by
    rw [← (p.commutes_base hb.1).eq, geom.1,mul_assoc,hz2,mul_one]
  have htQu : z*b ∈ coreInG s.u := he.symm ▸ geom.2.1.2
  have hzQt := core_reciprocity_base h htf (fusionCore_le z htA)
  have huQt := core_reciprocity h s.u_fused htf htQu
  have htQt : z*b ∈ coreInG (z*b) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp htf
    have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom h.involution_mem_coreInG
    rw [map_coreInG] at hh
    change g*z*g⁻¹ ∈ coreInG (g*z*g⁻¹) at hh
    exact hg ▸ hh
  have hbQt : b ∈ coreInG (z*b) := by
    have hh := (coreInG (z*b)).mul_mem hzQt htQt
    simpa only [← mul_assoc,hz2,one_mul] using hh
  have hzAt : z ∈ fusionCore (z*b) := subset_closure ⟨hzQt,htf.symm⟩
  have huAt : s.u ∈ fusionCore (z*b) := subset_closure ⟨huQt,htf.symm.trans s.u_fused⟩
  have hbAt : b ∈ fusionCore (z*b) := subset_closure ⟨hbQt,htf.symm.trans hbf⟩
  have hbEven : b ∈ s.markedAlternating := movedFour_le_markedAlternating s hb.1
  have huzEven : s.u*z ∈ s.markedAlternating := by
    apply (s.mem_markedAlternating_iff _ (s.S.mul_mem s.u_mem s.z_mem)).mpr
    rw [Equiv.Perm.mem_alternatingGroup]
    have he : (⟨s.u*z,s.S.mul_mem s.u_mem s.z_mem⟩ : s.S) =
        ⟨s.u,s.u_mem⟩ * ⟨z,s.z_mem⟩ := rfl
    rw [he,map_mul,map_mul,s.u_swap.sign_eq,s.z_swap.sign_eq]
    decide
  have hle : zpowers b ⊔ zpowers (s.u*z) ≤ s.evenFusion (z*b) :=
    sup_le (zpowers_le.mpr ⟨hbAt,hbEven⟩)
      (zpowers_le.mpr ⟨(fusionCore (z*b)).mul_mem huAt hzAt,huzEven⟩)
  have huzQ : s.u*z ∉ coreInG z := by
    intro hh
    exact selected_involution_not_core c
      ((mul_mem_cancel_right h.involution_mem_coreInG).mp hh)
  have huz1 : s.u*z ≠ 1 := fun he => huzQ (he ▸ (coreInG z).one_mem)
  have hbuz : b ≠ s.u*z := fun he => huzQ (he ▸ fusionCore_le z hbF)
  have huz2 : (s.u*z)*(s.u*z)=1 := by
    rw [← pow_two, (show Commute s.u z from c.u_commutes_z).mul_pow]
    simp only [pow_two,hu2,hz2,one_mul]
  have hcomm : Commute b (s.u*z) :=
    (show Commute b s.u from mem_centralizer_singleton_iff.mp hb.2).mul_right
      (p.commutes_base hb.1)
  have hfour := isKleinFour_closure_pair b (s.u*z) hb2 huz2 hb1 huz1 hbuz hcomm
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [sup_zpowers_eq_closure_pair,hfour.card_four]
  exact evenFusion_card_le_four s dt hzAt

end QuaternionExchange
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

end
