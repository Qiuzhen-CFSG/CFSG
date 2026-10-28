module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreLineAction
public import Theory.SpecificGroups.SL2.LineRootGeometry

/-!
# Intersections of neighboring point radicals

A nonzero vector of the supplied natural SL₂(4) module has a Sylow
two-subgroup as its stabilizer. The original three-copy multiplicity
coordinates therefore show that an E-fixed nonzero class in R/Z(R)
has no additional even stabilizers outside the marked image of E.

An element common to E and a neighboring radical lies in R, by regularity
on the original line. If its class modulo Z(R) were nonzero, the preceding
natural-module calculation would make the neighboring radical fix the
original point, contradicting its transitivity on the other four points.
Thus the intersection is precisely Z. All transports use the original
left-coset action and conjugation maps. The point stabilizer in E is E∩R,
with index four and order 2⁹.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (5.1)(2), pp.599–600,
DOI 10.1007/BF01232280. The natural action is the one retained in LocalData;
faithful irreducibility alone is not used to identify that action.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem

private theorem natural_fixed_mem_sylow
    (P : Sylow 2 Representation.SL2FourNatural.SL)
    (v : Representation.SL2FourNatural.V) (hv : v ≠ 0)
    (hP : ∀ g ∈ (P : Subgroup _), Representation.SL2FourNatural.action g v = v)
    (g : Representation.SL2FourNatural.SL)
    (hg : Representation.SL2FourNatural.action g v = v) : g ∈ P := by
  let W := Submodule.span Representation.SL2FourNatural.F ({v} : Set Representation.SL2FourNatural.V)
  have hW : Module.finrank Representation.SL2FourNatural.F W = 1 := finrank_span_singleton hv
  obtain ⟨Q,hQ⟩ := Matrix.SpecialLinearGroup.exists_sylow_fixing_line W hW
  have fixed (k : Representation.SL2FourNatural.SL)
      (hk : Representation.SL2FourNatural.action k v = v) :
      k ∈ fixingSubgroup Representation.SL2FourNatural.SL (W : Set Representation.SL2FourNatural.V) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    change Matrix.mulVec k.val (c • v) = c • v
    rw [Matrix.mulVec_smul]
    exact congrArg (c • ·) hk
  have hPQ : (P : Subgroup Representation.SL2FourNatural.SL) ≤ (Q : Subgroup Representation.SL2FourNatural.SL) := by
    rw [hQ]
    exact fun k hk => fixed k (hP k hk)
  have he : (P : Subgroup Representation.SL2FourNatural.SL) = (Q : Subgroup Representation.SL2FourNatural.SL) := (P.is_maximal' Q.isPGroup' hPQ).symm
  change g ∈ (P : Subgroup Representation.SL2FourNatural.SL)
  rw [he,hQ]
  exact fixed g hg

namespace LocalData
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)
attribute [local instance] ThreeSpaceData.R_normal_in_S_intrinsic

private theorem multiplicity_fixed_mem_sylow (w : a.d.multiplicitySpace) (hw : w ≠ 1)
    (hf : ∀ p ∈ (a.alternatingSylow : Subgroup (alternatingGroup (Fin 5))),
      a.d.markedMultiplicityAction h p w = w)
    (g : alternatingGroup (Fin 5)) (hg : a.d.markedMultiplicityAction h g w = w) :
    g ∈ a.alternatingSylow := by
  let := a.d.multiplicitySpace_elementary h
  let P := a.alternatingSylow.mapSurjective (f := a.alternatingEquiv.toMonoidHom)
    a.alternatingEquiv.surjective
  have hv : a.naturalEquiv (Additive.ofMul w) ≠ 0 := by
    intro he
    have hh := a.naturalEquiv.injective (he.trans (map_zero a.naturalEquiv).symm)
    exact hw (congrArg Additive.toMul hh)
  have hfix : ∀ k ∈ (P : Subgroup _),
      Representation.SL2FourNatural.action k (a.naturalEquiv (Additive.ofMul w)) =
        a.naturalEquiv (Additive.ofMul w) := by
    rintro k ⟨p,hp,rfl⟩
    exact (a.natural_equivariant p w).symm.trans (congrArg a.naturalEquiv (congrArg Additive.ofMul (hf p hp)))
  have hm := natural_fixed_mem_sylow P _ hv hfix (a.alternatingEquiv g)
    (by rw [←a.natural_equivariant,hg])
  obtain ⟨p,hp,he⟩ := hm
  exact a.alternatingEquiv.injective he ▸ hp

/-- In the literal radical quotient, a nonzero class fixed by E has no
additional even stabilizers outside the marked image of E. -/
theorem radical_fixed_even_mem_image (v : a.d.R ⧸ center a.d.R) (hv : v ≠ 1)
    (hf : ∀ e : a.P.E,
      a.d.radicalAction ⟨e, (a.line_normalizer ▸ a.E_le_line e.property)⟩ v = v)
    (s : a.d.S)
    (hs : a.d.SQuotientEquiv h (QuotientGroup.mk' _ s) ∈ alternatingGroup (Fin 5))
    (hsv : a.d.SRadicalAction h (QuotientGroup.mk' _ s) v = v) :
    a.d.SQuotientEquiv h (QuotientGroup.mk' _ s) ∈
      (a.alternatingSylow : Subgroup (alternatingGroup (Fin 5))).map
        (alternatingGroup (Fin 5)).subtype := by
  obtain ⟨f,_,hfcoord⟩ := a.d.exists_multiplicity_coordinates h
  obtain ⟨⟨u,w,t⟩,rfl⟩ := f.surjective v
  have heq (b : a.d.S ⧸ a.d.R.subgroupOf a.d.S)
      (hb : a.d.SRadicalAction h b (f (u,w,t)) = f (u,w,t)) :
      (a.d.multiplicityAction h b u, a.d.multiplicityAction h b w,
        a.d.multiplicityAction h b t) = (u,w,t) :=
    f.injective ((hfcoord b u w t).trans hb)
  have hsome : ∃ v : a.d.multiplicitySpace, v ≠ 1 ∧
      ∀ b : a.d.S ⧸ a.d.R.subgroupOf a.d.S,
        a.d.SRadicalAction h b (f (u,w,t)) = f (u,w,t) →
          a.d.multiplicityAction h b v = v := by
    by_cases hu : u = 1
    · by_cases hw : w = 1
      · refine ⟨t, ?_, fun b hb => congrArg (fun v => v.2.2) (heq b hb)⟩
        intro ht
        apply hv
        rw [hu,hw,ht]
        exact f.map_one
      · exact ⟨w,hw,fun b hb => congrArg (fun v => v.2.1) (heq b hb)⟩
    · exact ⟨u,hu,fun b hb => congrArg Prod.fst (heq b hb)⟩
  obtain ⟨v,hv,hfix⟩ := hsome
  have hP : ∀ p ∈ (a.alternatingSylow : Subgroup (alternatingGroup (Fin 5))),
      a.d.markedMultiplicityAction h p v = v := by
    intro p hp
    have hpim : (p : Equiv.Perm (Fin 5)) ∈
        (a.alternatingSylow : Subgroup (alternatingGroup (Fin 5))).map
          (alternatingGroup (Fin 5)).subtype := ⟨p,hp,rfl⟩
    rw [←a.E_quotient] at hpim
    obtain ⟨e,he,hep⟩ := hpim
    change a.d.SQuotientEquiv h (QuotientGroup.mk' _ e) = p at hep
    rw [←hep,a.d.markedMultiplicityAction_quotient]
    exact hfix _ (hf ⟨e,he⟩)
  have hg : a.d.markedMultiplicityAction h
      (a.d.SQuotientEquiv h (QuotientGroup.mk' _ s)) v = v := by
    rw [a.d.markedMultiplicityAction_quotient]
    exact hfix _ hsv
  exact ⟨⟨_,hs⟩,a.multiplicity_fixed_mem_sylow v hv hP ⟨_,hs⟩ hg,rfl⟩

private theorem radical_projection_mem (e : a.P.E) :
    a.lineProjection ⟨e,a.E_le_line e.property⟩ ∈
      (a.alternatingSylow : Subgroup (alternatingGroup (Fin 5))).map
        (alternatingGroup (Fin 5)).subtype := by
  rw [←a.E_quotient]
  let s : a.d.S := ⟨e,a.E_le_S e.property⟩
  exact ⟨s,e.property,(a.lineProjection_product 1 s _ (by simp [s])).symm⟩

private theorem core_conjugate_mem (y : Point a.P) (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1))
    (u : coreAt a.P y) :
    ∃ (n : a.L.G₂) (e : a.P.E), (u : G) = (n : G)*(e : G)*(n : G)⁻¹ := by
  obtain ⟨n,rfl,hn⟩ := hy
  have hnN := (Cosets.vertex_eq_base _ _).mp hn
  have hu := (coreAt_vertex a.P n).le u.property
  change n⁻¹*(u : G)*(n⁻¹)⁻¹ ∈ a.P.E at hu
  refine ⟨⟨n,hnN⟩,⟨n⁻¹*(u : G)*(n⁻¹)⁻¹,hu⟩,?_⟩
  simp only [inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]

private theorem core_on_line_le_S (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1)) : coreAt a.P y ≤ a.d.S := by
  intro u hu
  obtain ⟨n,e,he⟩ := a.core_conjugate_mem y hy ⟨u,hu⟩
  change u = (n : G)*(e : G)*(n : G)⁻¹ at he
  rw [he]
  exact (mem_normalizer_iff.mp (a.d.S_normalized (a.line_normalizer ▸ n.property)) e).mp
    (a.E_le_S e.property)

private theorem core_projection_even (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1)) (u : coreAt a.P y) :
    a.d.SQuotientEquiv h (QuotientGroup.mk' _ (⟨u,a.core_on_line_le_S y hy u.property⟩ : a.d.S)) ∈
      alternatingGroup (Fin 5) := by
  obtain ⟨n,e,he⟩ := a.core_conjugate_mem y hy u
  let v : a.L.G₂ := ⟨e,a.E_le_line e.property⟩
  let w : a.L.G₂ := ⟨u,a.line_normalizer.symm ▸ (Subgroup.centralizer_le_normalizer _)
    (a.core_on_line_le_S y hy u.property)⟩
  have hw : w = n*v*n⁻¹ := Subtype.ext he
  have hs := a.lineProjection_product 1 ⟨u,a.core_on_line_le_S y hy u.property⟩ w
    (by simp [w])
  rw [←hs,hw,map_mul,map_mul,map_inv]
  have hv : a.lineProjection v ∈ alternatingGroup (Fin 5) := by
    obtain ⟨p,_,hp⟩ := a.radical_projection_mem e
    exact hp ▸ p.property
  exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ hv _

private theorem core_commute (x : Point a.P) (u v : coreAt a.P x) :
    Commute (u : G) (v : G) := by
  let := a.P.E_elementary
  let : IsMulCommutative (coreAt a.P x) := by
    rw [←vertex_representative x,coreAt_vertex]
    exact a.P.E.comap_injective_isMulCommutative
      (MulAut.conj (representative x)⁻¹).injective
  exact (Commute.all u v).map (coreAt a.P x).subtype

private theorem radicalAction_fixed_of_commute (s : a.d.S) (r : a.d.R)
    (hc : Commute (s : G) (r : G)) :
    a.d.SRadicalAction h (QuotientGroup.mk' _ s) (QuotientGroup.mk' (center a.d.R) r) =
      QuotientGroup.mk' (center a.d.R) r := by
  rw [a.d.SRadicalAction_mk,a.d.radicalAction_mk]
  apply congrArg (QuotientGroup.mk' (center a.d.R))
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr hc.eq

/-- AS91 (5.1)(2): neighboring point radicals meet in the original three-space.
The common radical class has three natural-module coordinates. A nonzero
coordinate would force the neighboring radical to fix the original point,
contradicting its transitivity on the other four points. -/
theorem core_intersection_base (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1)) (hyx : y ≠ Cosets.vertex a.P.M 1) :
    a.P.E ⊓ coreAt a.P y = a.d.space := by
  apply le_antisymm
  · intro r hr
    have hrK : r ∈ a.d.K := by
      apply (a.point_action_kernel ⟨r,a.E_le_line hr.1⟩).mp
      intro b hb
      exact a.core_regular_base ⟨r,hr.1⟩ ⟨y,hy⟩ hyx
        ((coreAt_le_stabilizer a.P y) hr.2) ⟨b,hb⟩
    let r' : a.d.R := ⟨r,hrK,a.E_le_S hr.1⟩
    have hz : QuotientGroup.mk' (center a.d.R) r' = 1 := by
      by_contra hnon
      have hfix : ∀ e : a.P.E,
          a.d.radicalAction ⟨e,(a.line_normalizer ▸ a.E_le_line e.property)⟩
            (QuotientGroup.mk' (center a.d.R) r') = QuotientGroup.mk' (center a.d.R) r' := by
        intro e
        let := a.P.E_elementary
        exact a.radicalAction_fixed_of_commute ⟨e,a.E_le_S e.property⟩ r'
          ((Commute.all e ⟨r,hr.1⟩).map a.P.E.subtype)
      have hxfix (u : coreAt a.P y) :
          (u : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
        let s : a.d.S := ⟨u,a.core_on_line_le_S y hy u.property⟩
        have hu := a.radical_fixed_even_mem_image _ hnon hfix s (a.core_projection_even y hy u)
          (a.radicalAction_fixed_of_commute s r' (a.core_commute y u ⟨r,hr.2⟩))
        rw [←a.E_quotient] at hu
        obtain ⟨e,he,hes⟩ := hu
        change a.d.SQuotientEquiv h (QuotientGroup.mk' _ e) =
          a.d.SQuotientEquiv h (QuotientGroup.mk' _ s) at hes
        have hker : e⁻¹*s ∈ a.d.R.subgroupOf a.d.S := by
          exact QuotientGroup.eq.mp ((a.d.SQuotientEquiv h).injective hes)
        have hm : (s : G) ∈ a.P.M := by
          have hh : (e : G)*((e : G)⁻¹*(s : G)) ∈ a.P.M :=
            a.P.M.mul_mem (a.P.E_le he) (a.K_le_point hker.1)
          simpa only [mul_inv_cancel_left] using hh
        rw [Cosets.smul_vertex,mul_one]
        exact (Cosets.vertex_eq_base _ _).mpr hm
      have hx : OnLine a.L (Cosets.vertex a.P.M 1) (Cosets.vertex a.L.G₂ 1) := ⟨1,rfl,rfl⟩
      have hall : ∀ b : a.LinePoints, b.val = y ∨ b.val = Cosets.vertex a.P.M 1 := by
        intro b
        by_cases hby : b.val = y
        · exact Or.inl hby
        · obtain ⟨u,hu⟩ := a.core_transitive_other y _ hy _ b.val hx hyx.symm b.property hby
          exact Or.inr (hu.symm.trans (hxfix u))
      have hc : Nat.card a.LinePoints ≤ 2 := by
        classical
        let f : a.LinePoints → Bool := fun b => decide (b.val = y)
        have hf : Function.Injective f := by
          intro b c he
          have he' : (b.val = y) ↔ (c.val = y) := by
            simpa only [f,decide_eq_decide] using he
          apply Subtype.ext
          rcases hall b with hb | hb
          · exact hb.trans (he'.mp hb).symm
          · rcases hall c with hc | hc
            · exact (he'.mpr hc).trans hc.symm
            · exact hb.trans hc.symm
        simpa using Nat.card_le_card_of_injective f hf
      have hc5 : Nat.card a.LinePoints = 5 := a.line_card _
      omega
    rw [←a.d.R_center_eq_space h]
    exact ⟨r',(QuotientGroup.eq_one_iff _).mp hz,rfl⟩
  · intro r hr
    refine ⟨a.space_le_E hr,?_⟩
    obtain ⟨n,rfl,hn⟩ := hy
    rw [coreAt_vertex]
    change n⁻¹*r*(n⁻¹)⁻¹ ∈ a.P.E
    apply a.space_le_E
    have hnN : n ∈ normalizer (a.d.space : Set G) :=
      a.line_normalizer ▸ (Cosets.vertex_eq_base _ _).mp hn
    exact (mem_normalizer_iff.mp ((normalizer _).inv_mem hnN) r).mp hr

/-- Transport of the neighboring-radical intersection by the literal left action. -/
theorem core_intersection_at (g : G) (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ g)) (hyx : y ≠ Cosets.vertex a.P.M g) :
    coreAt a.P (Cosets.vertex a.P.M g) ⊓ coreAt a.P y =
      a.d.space.comap (MulAut.conj g⁻¹).toMonoidHom := by
  have hy' : OnLine a.L (g⁻¹ • y) (Cosets.vertex a.L.G₂ 1) := by
    simpa only [OnLine,Cosets.smul_vertex,inv_mul_cancel] using incident_smul g⁻¹ hy
  have hne : g⁻¹ • y ≠ Cosets.vertex a.P.M 1 := by
    intro he
    apply hyx
    have hh := congrArg (g • ·) he
    simpa only [smul_inv_smul,Cosets.smul_vertex,mul_one] using hh
  have he := congrArg (fun K : Subgroup G => K.comap (MulAut.conj g⁻¹).toMonoidHom)
    (a.core_intersection_base (g⁻¹ • y) hy' hne)
  rw [comap_inf,←coreAt_vertex,←coreAt_smul,smul_inv_smul] at he
  exact he

/-- The stabilizer in E of any other point on the original line is E∩R. -/
theorem radical_point_stabilizer (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1)) (hyx : y ≠ Cosets.vertex a.P.M 1) :
    (MulAction.stabilizer G y).subgroupOf a.P.E = a.d.R.subgroupOf a.P.E := by
  ext e
  constructor
  · intro he
    refine ⟨?_,a.E_le_S e.property⟩
    apply (a.point_action_kernel ⟨e,a.E_le_line e.property⟩).mp
    intro b hb
    exact a.core_regular_base e ⟨y,hy⟩ hyx he ⟨b,hb⟩
  · intro he
    exact (a.point_action_kernel ⟨e,a.E_le_line e.property⟩).mpr he.1 y hy

private theorem radical_quotient_index : (a.d.R.subgroupOf a.P.E).index = 4 := by
  let f : a.P.E →* Equiv.Perm a.LinePoints :=
    a.linePointAction.comp (inclusion a.E_le_line)
  have hk : f.ker = a.d.R.subgroupOf a.P.E := by
    ext e
    change a.linePointAction (inclusion a.E_le_line e) = 1 ↔ (e : G) ∈ a.d.R
    rw [←MonoidHom.mem_ker,a.linePointAction_ker]
    exact ⟨fun he => ⟨he,a.E_le_S e.property⟩,fun he => he.1⟩
  have hr : f.range = (a.P.E.subgroupOf a.L.G₂).map a.linePointAction := by
    ext p
    constructor
    · rintro ⟨e,rfl⟩
      exact ⟨inclusion a.E_le_line e,e.property,rfl⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨⟨e,he⟩,rfl⟩
  rw [←hk,index_ker,hr]
  exact a.radical_line_action_card

/-- AS91 (5.1)(2), the literal index four point-stabilizer assertion. -/
theorem radical_point_stabilizer_index (y : Point a.P)
    (hy : OnLine a.L y (Cosets.vertex a.L.G₂ 1)) (hyx : y ≠ Cosets.vertex a.P.M 1) :
    ((MulAction.stabilizer G y).subgroupOf a.P.E).index = 4 := by
  rw [a.radical_point_stabilizer y hy hyx]
  exact a.radical_quotient_index

/-- The original point radical meets R in a group of order 2⁹. -/
theorem radical_R_card : Nat.card (a.d.R.subgroupOf a.P.E) = 512 := by
  have hc := (a.d.R.subgroupOf a.P.E).card_mul_index
  rw [a.radical_quotient_index,a.P.E_card] at hc
  omega


end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
