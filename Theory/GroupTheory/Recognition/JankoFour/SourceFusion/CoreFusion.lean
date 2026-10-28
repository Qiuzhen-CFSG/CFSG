module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.CoreLifts
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.CorePair
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreOrbits

/-!
# Two involution classes with conjugators in the original join

A pair displacement in the native sextet core supplies a second-orbit
element of E intersect Q. The original returning marker r also lies in E
intersect Q, and Thompson fusion gives its conjugator in M. These two
elements occupy different noncentral H-classes in Q because z and t are
not conjugate in G. The proved two-class core coverage therefore fuses every
core involution to z or t, using only H and M conjugators. The four Todd
lifts and the original Sylow subgroup extend this to every involution of
H joined with M, and then to ambient two-class coverage. No simplicity of
the join is used.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (4.2), (6.4), p.602.
-/

public section
open Subgroup Sporadic.Mathieu MathieuCode
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open LocalGeometry LocalGeometry.LocalSubgroups SourceIncidence SourceRecognition
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- A pair displacement supplies a second-orbit element in E intersect Q. -/
lemma second_into_core (a : LocalData h) :
    ∃ m ∈ a.P.M, MulAut.conj m (second a) ∈ ambientCore z := by
  obtain ⟨s,hs,v,B,hB⟩ := J4Fusion.sextet_core_pair_displacement a.sextet
  let q := toddSection a s
  let w := a.P.vectorEmbedding (Multiplicative.ofAdd v)
  have hq : q ∈ ambientCore z := toddSection_core a s hs
  have hwE : w ∈ a.P.E := ⟨_,rfl⟩
  have hwn : w ∈ normalizer (ambientCore z : Set G) :=
    (normalizer_ambientCore h).symm ▸ a.radical_le_plane hwE
  have hc : q*w*q⁻¹*w⁻¹ ∈ ambientCore z := by
    have hh := (ambientCore z).mul_mem hq
      ((mem_normalizer_iff.mp hwn q⁻¹).mp ((ambientCore z).inv_mem hq))
    simpa only [mul_assoc] using hh
  have he : a.P.vectorEmbedding (Multiplicative.ofAdd (pairVector B)) = q*w*q⁻¹*w⁻¹ := by
    rw [←hB]
    have hh := vector_conj a.P ⟨q,toddSection_mem a s⟩ v
    rw [toddSection_projection] at hh
    calc
      _ = a.P.vectorEmbedding (Multiplicative.ofAdd (cocodeRepresentation s v)) * w⁻¹ := by
        rw [←map_inv,←map_mul]
        congr 1
        exact congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _)
      _ = q*w*q⁻¹*w⁻¹ := congrArg (fun x : G => x*w⁻¹) hh.symm
  obtain ⟨g,hg⟩ := weightTwoOrbit_transitive ⟨{0,1},by decide⟩ B
  obtain ⟨m,hm⟩ := a.projection_surjective g
  refine ⟨m,m.property,?_⟩
  rw [second,vector_conj,hm,hg,he]
  exact hc

private lemma core_central_eq (h : IsTypeJ4 z) (q : core z)
    (hq : q ∈ center (core z)) : ((q : centralizer z) : G) = 1 ∨
      ((q : centralizer z) : G) = z := by
  have hh : ((q : centralizer z) : G) ∈ zpowers z := by
    rw [←core_center_image h]
    exact ⟨q.val,⟨q,hq,rfl⟩,rfl⟩
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,h.involution] at hh
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (he.symm.trans (pow_zero z))
  · exact Or.inr (he.symm.trans (pow_one z))

omit [Finite G] in
private lemma join_conj_trans (K : Subgroup G) {x y w : G}
    (hxy : ∃ k ∈ K, MulAut.conj k x = y)
    (hyw : ∃ k ∈ K, MulAut.conj k y = w) :
    ∃ k ∈ K, MulAut.conj k x = w := by
  obtain ⟨k,hk,hke⟩ := hxy
  obtain ⟨l,hl,hle⟩ := hyw
  refine ⟨l*k,K.mul_mem hl hk,?_⟩
  calc
    MulAut.conj (l*k) x = MulAut.conj l (MulAut.conj k x) := by
      simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]
    _ = w := by rw [hke,hle]

/-- The two noncentral H-classes in Q are represented by returning marker
and pair elements. Their conjugators, together with the two M-fusions, stay
inside H joined with M. -/
lemma core_involution_fusion (a : LocalData h) (u : G)
    (huQ : u ∈ ambientCore z) (hu : orderOf u = 2) :
    (∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k z = u) ∨
    ∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k (second a) = u := by
  let K := centralizer z ⊔ a.P.M
  let := h.extraspecial
  obtain ⟨q,hq,hqu⟩ := huQ
  let qQ : core z := ⟨q,hq⟩
  have hqo : orderOf qQ = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
    change orderOf q.val = 2
    change q.val = u at hqu
    rw [hqu,hu]
  have qcoe : ((qQ : centralizer z) : G) = u := hqu
  by_cases hqc : qQ ∈ center (core z)
  · rcases core_central_eq h qQ hqc with he | he
    · exact ((orderOf_eq_prime_iff.mp hu).2 (qcoe.symm.trans he)).elim
    · refine Or.inl ⟨1,K.one_mem,?_⟩
      simpa only [map_one,MulAut.one_apply] using he.symm.trans qcoe
  obtain ⟨m,hm,hmt⟩ := second_into_core a
  let t := MulAut.conj m (second a)
  obtain ⟨tH,htQ,htcoe⟩ := hmt
  let tQ : core z := ⟨tH,htQ⟩
  have tcoe : ((tQ : centralizer z) : G) = t := htcoe
  have hto : orderOf tQ = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe,tcoe]
    exact ((MulAut.conj m).orderOf_eq (second a)).trans (second_order a)
  have htc : tQ ∉ center (core z) := by
    intro ht
    rcases core_central_eq h tQ ht with he | he
    · have h1 : tQ = 1 := Subtype.ext (Subtype.ext he)
      have hne := (orderOf_eq_prime_iff.mp hto).2
      exact hne h1
    · apply not_isConj_second a
      have ht : IsConj (second a) t := isConj_iff.mpr ⟨m,rfl⟩
      rw [tcoe.symm.trans he] at ht
      exact ht.symm
  let rQ := a.d.rInCore
  have rcoe : ((rQ : centralizer z) : G) = a.d.r := rfl
  have hro : orderOf rQ = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe,rcoe]
    obtain ⟨k,hk⟩ := isConj_iff.mp a.d.r_conj
    rw [←hk]
    exact ((MulAut.conj k).orderOf_eq z).trans h.involution
  have hrc : rQ ∉ center (core z) := by
    intro hr
    rcases core_central_eq h rQ hr with he | he
    · have h1 : rQ = 1 := Subtype.ext (Subtype.ext he)
      exact (orderOf_eq_prime_iff.mp hro).2 h1
    · exact a.d.r_ne (rcoe.symm.trans he)
  have hrE : a.d.r ∈ a.P.E := a.space_le_E (by
    rw [ThreeSpaceData.space,a.d.generated]
    exact subset_closure (by simp))
  obtain ⟨n,hn,hne⟩ := a.controls_marker_fusion hrE a.d.r_conj
  have hzR : ∃ k ∈ K, MulAut.conj k z = a.d.r := ⟨n,mem_sup_right hn,hne⟩
  have htT : ∃ k ∈ K, MulAut.conj k (second a) = t := ⟨m,mem_sup_right hm,rfl⟩
  have hrt : ¬ IsConj (rQ : centralizer z) (tQ : centralizer z) := by
    intro he
    have hamb := (centralizer z).subtype.map_isConj he
    change IsConj a.d.r tH.val at hamb
    change IsConj a.d.r ((tQ : centralizer z) : G) at hamb
    rw [tcoe] at hamb
    exact not_isConj_second a ((a.d.r_conj.trans hamb).trans
      (isConj_iff.mpr ⟨m,rfl⟩ : IsConj (second a) t).symm)
  obtain ⟨r₁,r₂,_,_,_,_,_,_,hcover⟩ := source_involution_orbit_cover h a.e a.X
  have hclass : IsConj (qQ : centralizer z) (rQ : centralizer z) ∨
      IsConj (qQ : centralizer z) (tQ : centralizer z) := by
    rcases hcover rQ hro hrc with hr | hr <;>
      rcases hcover tQ hto htc with ht | ht
    · exact (hrt (hr.trans ht.symm)).elim
    · rcases hcover qQ hqo hqc with hq | hq
      · exact Or.inl (hq.trans hr.symm)
      · exact Or.inr (hq.trans ht.symm)
    · rcases hcover qQ hqo hqc with hq | hq
      · exact Or.inr (hq.trans ht.symm)
      · exact Or.inl (hq.trans hr.symm)
    · exact (hrt (hr.trans ht.symm)).elim
  have transport (v : core z) (hv : IsConj (qQ : centralizer z) (v : centralizer z)) :
      ∃ k ∈ K, MulAut.conj k ((v : centralizer z) : G) = u := by
    obtain ⟨k,hk⟩ := isConj_iff.mp hv.symm
    refine ⟨k,mem_sup_left k.property,?_⟩
    exact (congrArg Subtype.val hk).trans qcoe
  rcases hclass with hr | ht
  · exact Or.inl (join_conj_trans K hzR (transport rQ hr))
  · exact Or.inr (join_conj_trans K htT (by simpa only [tcoe] using transport tQ ht))

/-- AS91 (6.4) inside the original centralizer-point join, with every
conjugator retained in that join. No simplicity of the join is assumed. -/
lemma join_involution_fusion (a : LocalData h) (u : G)
    (huK : u ∈ centralizer z ⊔ a.P.M) (hu : orderOf u = 2) :
    (∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k z = u) ∨
    ∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k (second a) = u := by
  rcases join_involution_representatives a u huK hu with hz | ht | ⟨b,e,k,hk,hku⟩
  · exact Or.inl hz
  · exact Or.inr ht
  · obtain ⟨m,hm,hmQ⟩ := pointLift_into_core a b e
    have ho : orderOf (MulAut.conj m (pointLift a b e)) = 2 :=
      ((MulAut.conj m).orderOf_eq _).trans (pointLift_order a b e)
    have hb : ∃ n ∈ centralizer z ⊔ a.P.M,
        MulAut.conj n (MulAut.conj m (pointLift a b e)) = u := by
      refine ⟨k*m⁻¹,(centralizer z ⊔ a.P.M).mul_mem hk
        ((centralizer z ⊔ a.P.M).inv_mem (mem_sup_right hm)),?_⟩
      simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc,
        inv_mul_cancel_left,mul_inv_cancel_left] using hku
    exact (core_involution_fusion a _ hmQ ho).elim
      (fun hh => Or.inl (join_conj_trans _ hh hb))
      (fun hh => Or.inr (join_conj_trans _ hh hb))

/-- AS91 (6.4), including separation of the two ambient classes. -/
lemma involution_classes (a : LocalData h) :
    ¬ IsConj z (second a) ∧ ∀ u : G, orderOf u = 2 →
      IsConj z u ∨ IsConj (second a) u := by
  refine ⟨not_isConj_second a,?_⟩
  intro u hu
  obtain ⟨v,hv⟩ := a.T.exists_isConj_of_orderOf_eq_prime_pow
    (hu.trans (pow_one 2).symm)
  have hvo : orderOf (v : G) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hv
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq u).trans hu
  have hvM : (v : G) ∈ a.P.M := (a.sylow_le v.property).1.2
  rcases join_involution_fusion a v (mem_sup_right hvM) hvo with ⟨k,_,he⟩ | ⟨k,_,he⟩
  · exact Or.inl ((isConj_iff.mpr ⟨k,he⟩).trans hv.symm)
  · exact Or.inr ((isConj_iff.mpr ⟨k,he⟩).trans hv.symm)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
