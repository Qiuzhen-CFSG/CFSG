module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineAction
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five

/-!
# The radical action on the other four points of a line

The two faithful S₅ quotient actions are identified through their equal
kernels. Under that identification, the stipulated image of E in the same
S/R marking gives an even permutation subgroup of order four on the actual
line points. An even involution on five points fixing two points is trivial.
Hence evaluation away from E's own point is injective, and the equal orders
make it bijective. Transport by the literal ambient action proves both
regularity (allowing the kernel) and transitivity in the unchanged Input.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.1)–(5.2),
pp.599–600, DOI 10.1007/BF01232280. No arbitrary S₅ marking or geometric
regularity hypothesis replaces the original quotient image.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)
attribute [local instance] ThreeSpaceData.R_normal_in_S_intrinsic

private noncomputable def lineActionEquiv : Equiv.Perm (Fin 5) ≃* Equiv.Perm a.LinePoints :=
  (QuotientGroup.quotientKerEquivOfSurjective a.lineProjection a.lineProjection_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (a.lineProjection_ker.trans a.linePointAction_ker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective a.linePointAction a.linePointAction_surjective))

private theorem lineActionEquiv_apply (n : a.L.G₂) :
    a.lineActionEquiv (a.lineProjection n) = a.linePointAction n := by
  let f := QuotientGroup.quotientKerEquivOfSurjective a.lineProjection a.lineProjection_surjective
  have he : f (QuotientGroup.mk n) = a.lineProjection n := rfl
  change (QuotientGroup.quotientKerEquivOfSurjective a.linePointAction a.linePointAction_surjective)
    (QuotientGroup.quotientMulEquivOfEq (a.lineProjection_ker.trans a.linePointAction_ker.symm) (f.symm (a.lineProjection n))) = _
  rw [←he,MulEquiv.symm_apply_apply,QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem radical_projection_image :
    (a.P.E.subgroupOf a.L.G₂).map a.lineProjection =
      (a.alternatingSylow : Subgroup (alternatingGroup (Fin 5))).map
        (alternatingGroup (Fin 5)).subtype := by
  rw [←a.E_quotient]
  ext p
  constructor
  · rintro ⟨n,hn,rfl⟩
    let s : a.d.S := ⟨n,a.E_le_S hn⟩
    refine ⟨s,hn,?_⟩
    exact (a.lineProjection_product 1 s n (by simp [s])).symm
  · rintro ⟨s,hs,rfl⟩
    let n : a.L.G₂ := ⟨s,a.E_le_line hs⟩
    exact ⟨n,hs,a.lineProjection_product 1 s n (by simp [n])⟩

/-- The radical induces a group of order four on the actual five line points. -/
theorem radical_line_action_card : Nat.card ((a.P.E.subgroupOf a.L.G₂).map a.linePointAction) = 4 := by
  have he : a.linePointAction = a.lineActionEquiv.toMonoidHom.comp a.lineProjection := by
    apply MonoidHom.ext; intro n; exact (a.lineActionEquiv_apply n).symm
  rw [he,←map_map,card_map_of_injective a.lineActionEquiv.injective,a.radical_projection_image,
    card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective]
  exact Theory.PSL2.SylowFixedQuotients.alternating_sylow_card a.alternatingSylow

private theorem radical_line_action_even [Fintype a.LinePoints] [DecidableEq a.LinePoints] (n : a.L.G₂) (hn : (n : G) ∈ a.P.E) :
    a.linePointAction n ∈ alternatingGroup a.LinePoints := by
  have hq : a.lineProjection n ∈ alternatingGroup (Fin 5) := by
    have hh : a.lineProjection n ∈ (a.P.E.subgroupOf a.L.G₂).map a.lineProjection := ⟨n,hn,rfl⟩
    rw [a.radical_projection_image] at hh
    obtain ⟨k,_,hk⟩ := hh
    exact hk ▸ k.property
  have he : (alternatingGroup (Fin 5)).map a.lineActionEquiv.toMonoidHom = alternatingGroup a.LinePoints := by
    rw [←alternatingGroup.commutator_perm_eq (by simp),map_commutator_eq,
      a.lineActionEquiv.toMonoidHom.range_eq_top_of_surjective a.lineActionEquiv.surjective,
      ←commutator_def,alternatingGroup.commutator_perm_eq (by
        rw [show Nat.card a.LinePoints = 5 from a.line_card _])]
  rw [←he]
  exact ⟨a.lineProjection n,hq,a.lineActionEquiv_apply n⟩

private theorem five_even_involution (p : Equiv.Perm (Fin 5)) (x y : Fin 5)
    (hp : p*p=1) (he : Equiv.Perm.sign p = 1) (hx : p x = x) (hy : p y = y) (hne : x ≠ y) : p=1 := by
  revert p x y; decide +kernel

private theorem even_involution_two_fixed {β : Type*} [Fintype β] [DecidableEq β] (hc : Nat.card β = 5)
    (p : Equiv.Perm β) (x y : β) (hp : p*p=1) (he : p ∈ alternatingGroup β)
    (hx : p x = x) (hy : p y = y) (hne : x ≠ y) : p=1 := by
  classical
  let f : β ≃ Fin 5 := Fintype.equivFinOfCardEq (by rwa [←Nat.card_eq_fintype_card])
  have hh : f.permCongr p = 1 := five_even_involution _ (f x) (f y)
    (by change f.permCongrHom p * f.permCongrHom p = 1; rw [←map_mul,hp,map_one]) (by rw [Equiv.Perm.sign_permCongr]; exact he)
    (by simp [hx]) (by simp [hy]) (f.injective.ne hne)
  exact f.permCongr.injective (hh.trans (map_one f.permCongrHom).symm)

/-- At the base line, an element of E fixing a second point fixes all five points. -/
theorem core_regular_base (u : a.P.E) (y : a.LinePoints)
    (hy : y.val ≠ Cosets.vertex a.P.M 1) (hu : (u : G) • y.val = y.val) :
    ∀ b : a.LinePoints, (u : G) • b.val = b.val := by
  classical
  let := Fintype.ofFinite a.LinePoints
  let := a.P.E_elementary
  let n : a.L.G₂ := ⟨u,a.E_le_line u.property⟩
  let x : a.LinePoints := ⟨Cosets.vertex a.P.M 1,⟨1,rfl,rfl⟩⟩
  have hn2 : n*n=1 := by
    apply Subtype.ext
    exact congrArg (fun v : a.P.E => (v : G)) (by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 a.P.E) u)
  have hx : a.linePointAction n x = x := by
    apply Subtype.ext
    rw [a.linePointAction_apply]
    change (u : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr (a.P.E_le u.property)
  have he : a.linePointAction n = 1 := even_involution_two_fixed (show Nat.card a.LinePoints = 5 from a.line_card _)
    _ x y (by rw [←map_mul,hn2,map_one]) (a.radical_line_action_even n u.property) hx
    (Subtype.ext (by rw [a.linePointAction_apply]; exact hu)) (fun hh => hy (congrArg Subtype.val hh.symm))
  intro b
  have hb := congrArg Subtype.val (Equiv.congr_fun he b)
  rw [a.linePointAction_apply] at hb
  exact hb

/-- The actual radical is transitive on the four points other than its own
point on the base line. The quotient marking gives order four, and the
fixed-point calculation gives injectivity of each evaluation map. -/
theorem core_transitive_base (y b : a.LinePoints)
    (hy : y.val ≠ Cosets.vertex a.P.M 1) (hb : b.val ≠ Cosets.vertex a.P.M 1) :
    ∃ u : a.P.E, (u : G) • y.val = b.val := by
  classical
  let := Fintype.ofFinite a.LinePoints
  let x : a.LinePoints := ⟨Cosets.vertex a.P.M 1,⟨1,rfl,rfl⟩⟩
  let J := (a.P.E.subgroupOf a.L.G₂).map a.linePointAction
  have fix (p : J) : (p : Equiv.Perm a.LinePoints) x = x := by
    obtain ⟨n,hn,hnp⟩ := p.property
    apply Subtype.ext
    rw [←hnp,a.linePointAction_apply]
    change (n : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr (a.P.E_le hn)
  let f : J → {v : a.LinePoints // v ≠ x} := fun p => ⟨p.val y,by
    intro he
    have hh := p.val.injective (he.trans (fix p).symm)
    exact hy (congrArg Subtype.val hh)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hpq' : p.val y = q.val y := congrArg Subtype.val hpq
    have ht : (p⁻¹*q : J).val y = y := by
      change p.val.symm (q.val y) = y
      rw [←hpq',Equiv.symm_apply_apply]
    obtain ⟨n,hn,hnpq⟩ := (p⁻¹*q : J).property
    have hny : (n : G) • y.val = y.val := by
      have hh := congrArg Subtype.val ht
      rw [←hnpq,a.linePointAction_apply] at hh
      exact hh
    have hall := a.core_regular_base (⟨n,hn⟩ : a.P.E) y hy hny
    have he : (p⁻¹*q : J) = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro v
      apply Subtype.ext
      rw [←hnpq,a.linePointAction_apply]
      exact hall v
    exact inv_mul_eq_one.mp he
  have hc : Nat.card {v : a.LinePoints // v ≠ x} = 4 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
      ←Nat.card_eq_fintype_card,show Nat.card a.LinePoints = 5 from a.line_card _]
  have hs : Function.Surjective f := ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf,a.radical_line_action_card.trans hc.symm⟩).2
  obtain ⟨p,hp⟩ := hs ⟨b,fun he => hb (congrArg Subtype.val he)⟩
  obtain ⟨n,hn,hnp⟩ := p.property
  refine ⟨⟨n,hn⟩,?_⟩
  have hh : (p : Equiv.Perm a.LinePoints) y = b := congrArg Subtype.val hp
  have hv := congrArg Subtype.val hh
  rw [←hnp,a.linePointAction_apply] at hv
  exact hv

/-- The unchanged regularity field on every ambient line. -/
theorem core_regular_other (x : Point a.P) (l : Line a.L) (hxl : OnLine a.L x l)
    (u : coreAt a.P x) (y : Point a.P) (hy : OnLine a.L y l) (hyx : y ≠ x)
    (huy : (u : G) • y = y) : ∀ b, OnLine a.L b l → (u : G) • b = b := by
  obtain ⟨g,rfl,rfl⟩ := hxl
  have he : g⁻¹*(u : G)*g ∈ a.P.E := by
    have hh := (coreAt_vertex a.P g).le u.property
    change g⁻¹*(u : G)*(g⁻¹)⁻¹ ∈ a.P.E at hh
    simpa only [inv_inv] using hh
  let e : a.P.E := ⟨g⁻¹*(u : G)*g,he⟩
  have hy' : OnLine a.L (g⁻¹ • y) (Cosets.vertex a.L.G₂ 1) := by
    simpa only [OnLine,Cosets.smul_vertex,inv_mul_cancel] using incident_smul g⁻¹ hy
  have hne : g⁻¹ • y ≠ Cosets.vertex a.P.M 1 := by
    intro hh
    have hh' := congrArg (g • ·) hh
    apply hyx
    simpa only [smul_inv_smul,Cosets.smul_vertex,mul_one] using hh'
  have hef : (e : G) • (g⁻¹ • y) = g⁻¹ • y := by
    change (g⁻¹*(u : G)*g) • (g⁻¹ • y) = _
    rw [mul_smul,mul_smul,smul_inv_smul,huy]
  intro b hb
  have hb' : OnLine a.L (g⁻¹ • b) (Cosets.vertex a.L.G₂ 1) := by
    simpa only [OnLine,Cosets.smul_vertex,inv_mul_cancel] using incident_smul g⁻¹ hb
  have hh := a.core_regular_base e ⟨g⁻¹ • y,hy'⟩ hne hef ⟨g⁻¹ • b,hb'⟩
  change (g⁻¹*(u : G)*g) • (g⁻¹ • b) = g⁻¹ • b at hh
  have hv := congrArg (g • ·) hh
  simpa only [mul_smul,smul_inv_smul] using hv

/-- The unchanged transitivity field on the other four points of every line. -/
theorem core_transitive_other (x : Point a.P) (l : Line a.L) (hxl : OnLine a.L x l)
    (y b : Point a.P) (hy : OnLine a.L y l) (hyx : y ≠ x)
    (hb : OnLine a.L b l) (hbx : b ≠ x) : ∃ u : coreAt a.P x, (u : G) • y = b := by
  obtain ⟨g,rfl,rfl⟩ := hxl
  have trans (v : Point a.P) (hv : OnLine a.L v (Cosets.vertex a.L.G₂ g)) :
      OnLine a.L (g⁻¹ • v) (Cosets.vertex a.L.G₂ 1) := by
    simpa only [OnLine,Cosets.smul_vertex,inv_mul_cancel] using incident_smul g⁻¹ hv
  have ne (v : Point a.P) (hv : v ≠ Cosets.vertex a.P.M g) :
      g⁻¹ • v ≠ Cosets.vertex a.P.M 1 := by
    intro hh
    have hh' := congrArg (g • ·) hh
    apply hv
    simpa only [smul_inv_smul,Cosets.smul_vertex,mul_one] using hh'
  obtain ⟨e,he⟩ := a.core_transitive_base ⟨g⁻¹ • y,trans y hy⟩ ⟨g⁻¹ • b,trans b hb⟩
    (ne y hyx) (ne b hbx)
  have hm : g*(e : G)*g⁻¹ ∈ coreAt a.P (Cosets.vertex a.P.M g) := by
    rw [coreAt_vertex]
    change g⁻¹*(g*(e : G)*g⁻¹)*(g⁻¹)⁻¹ ∈ a.P.E
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using e.property
  refine ⟨⟨g*(e : G)*g⁻¹,hm⟩,?_⟩
  have hh := congrArg (g • ·) he
  change (g*(e : G)*g⁻¹) • y = b
  simpa only [mul_smul,smul_inv_smul] using hh

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
