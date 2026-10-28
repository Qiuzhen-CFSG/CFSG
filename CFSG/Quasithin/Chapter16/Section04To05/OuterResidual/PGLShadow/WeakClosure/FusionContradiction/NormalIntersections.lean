module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Complement
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Normal intersections in the weak-closure contradiction

For the genuine intersection setup and marked centralizer geometry, the two
central lines are Z(T) ∩ T_L = ⟨v⟩ and Z(T) ∩ T_C = ⟨z⟩. Distinct
normalizer conjugates of the latter line give disjoint conjugates of T_C:
a nontrivial normal intersection in the two-group T would meet Z(T).
The same argument gives T_L ∩ T_C^k = 1, so T_C^k centralizes T_L.
Its actual conjugation action on the PSL₂ carrier is faithful and fixes the
actual image of T_L pointwise. We also construct the genuine intersection
setup with R = T_C^k, so earlier noncontainment results apply to it.

The marked reflection puts v in [T,T], and normalizer fusion then puts z
there too. These deductions are conditional on the two normalizer conjugators.
`FusionConjugators` is their output specification, not a source hypothesis.
The Burnside orbit construction, the pointwise-centralizer cardinality step,
and the derived/Frattini contradiction are not asserted by this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.6, printed p.1185, first two paragraphs.
All conjugation is left conjugation and normality is relative to T.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup GorensteinWalter
open scoped Pointwise commutatorElement
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
variable {T : Sylow 2 G} {z g r v : G} {L R : Subgroup G}

/-- The two normalizer conjugators obtained from failure of weak closure.
This is intermediate output, not an additional source hypothesis. -/
structure FusionConjugators (T : Sylow 2 G) (z v : G) where
  first : G
  second : G
  first_normalizes : first ∈ normalizer (T : Set G)
  second_normalizes : second ∈ normalizer (T : Set G)
  first_z : MulAut.conj first z = v
  second_z : MulAut.conj second z = v * z

private theorem mem_zpowers_two {a x : G} (ha : orderOf a = 2) :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, he⟩
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, by omega, by simp⟩

omit [Finite G] in
private theorem ne_one_of_order_two {a : G} (ha : orderOf a = 2) : a ≠ 1 := by
  intro he
  simp [he] at ha

omit [Finite G] in
/-- The actual component is centerless, by transport from PSL₂. -/
theorem component_inf_centralizer_eq_bot (e : L ≃* PSL2 F) :
    L ⊓ centralizer (L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hc : (⟨x, hx.1⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx.2 y y.property)
  have hmodel : e ⟨x, hx.1⟩ ∈ center (PSL2 F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hc y)
  rw [psl2_center_eq_bot, mem_bot] at hmodel
  have he : (⟨x, hx.1⟩ : L) = 1 := e.injective (by simpa using hmodel)
  exact congrArg Subtype.val he

/-- Normality is relative to T throughout this argument. -/
theorem sylow_normalizes_component_and_commuting (h : IntersectionSetup T z L g R) :
    (T : Subgroup G) ≤ normalizer (componentSylow T L : Set G) ∧
    (T : Subgroup G) ≤ normalizer (commutingSylow T L : Set G) := by
  exact ⟨(le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf,
    (le_inf (T : Subgroup G).le_normalizer
      (h.sylow_normalizes.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf⟩

omit [Finite G] in
/-- A normalizer of T carries a relatively normal subgroup to another one. -/
theorem conjugate_normal_in_sylow {A : Subgroup G} {a : G}
    (hA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (ha : a ∈ normalizer (T : Set G)) :
    (T : Subgroup G) ≤ normalizer (A.conjBy a : Set G) := by
  have hm := map_mono (f := (MulAut.conj a).toMonoidHom) hA
  have he : (T : Subgroup G).map (MulAut.conj a).toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ha
  rw [map_equiv_normalizer_eq, he] at hm
  exact hm

omit [Finite G] in
theorem conjugate_le_sylow {A : Subgroup G} {a : G}
    (hA : A ≤ (T : Subgroup G)) (ha : a ∈ normalizer (T : Set G)) :
    A.conjBy a ≤ (T : Subgroup G) := by
  have hm := map_mono (f := (MulAut.conj a).toMonoidHom) hA
  have he : (T : Subgroup G).map (MulAut.conj a).toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ha
  rwa [he] at hm

/-- The component line in the center follows directly from C_{T_L}(r). -/
theorem component_inf_center (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (d : CentralizerGeometry T z L r v) :
    componentSylow T L ⊓ embeddedCenter (T : Subgroup G) = zpowers v := by
  apply le_antisymm
  · intro x hx
    rw [← d.component_fixed]
    exact ⟨hx.1, mem_centralizer_singleton_iff.mpr
      (hx.2.2 r (h.le_sylow hr)).symm⟩
  · apply le_inf (zpowers_le.mpr d.v_mem)
    rw [d.center_eq]
    exact le_sup_right

/-- The complementary line in the center is the actual ⟨z⟩. -/
theorem commuting_inf_center (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v) :
    commutingSylow T L ⊓ embeddedCenter (T : Subgroup G) = zpowers z := by
  have hzC := h.toStandardSetup.z_mem_commutingSylow
  have hzv : Commute z v :=
    (mem_centralizer_singleton_iff.mp (h.sylow_centralizes d.v_mem.1)).symm
  have hn : zpowers v ≤ normalizer (zpowers z : Set G) := by
    apply (le_trans · (centralizer_le_normalizer _))
    rw [zpowers_eq_closure z, centralizer_closure]
    exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzv.symm)
  apply le_antisymm
  · intro x hx
    have hxZ : x ∈ (zpowers z : Set G) * (zpowers v : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
      exact d.center_eq ▸ hx.2
    obtain ⟨a, ha, b, hb, rfl⟩ := hxZ
    have haC := (zpowers_le.mpr hzC) ha
    have hbC : b ∈ commutingSylow T L := by
      simpa only [inv_mul_cancel_left] using
        (commutingSylow T L).mul_mem ((commutingSylow T L).inv_mem haC) hx.1
    have hbL : b ∈ L := (zpowers_le.mpr d.v_mem.2) hb
    have hb1 : b = 1 := by
      have hm : b ∈ L ⊓ centralizer (L : Set G) := ⟨hbL, hbC.2⟩
      simpa only [component_inf_centralizer_eq_bot e, mem_bot] using hm
    change a * b ∈ zpowers z
    rw [hb1, mul_one]
    exact ha
  · apply le_inf (zpowers_le.mpr hzC)
    rw [d.center_eq]
    exact le_sup_left

/-- The two marked central involutions are different. -/
theorem marked_central_involutions_ne (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v) : z ≠ v := by
  intro he
  have hm : v ∈ L ⊓ centralizer (L : Set G) :=
    ⟨d.v_mem.2, he ▸ h.toStandardSetup.z_mem_commutingSylow.2⟩
  have hv1 : v = 1 := by simpa only [component_inf_centralizer_eq_bot e, mem_bot] using hm
  exact ne_one_of_order_two d.v_order hv1

private theorem conjugate_commuting_inf_center (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    {a : G} (ha : a ∈ normalizer (T : Set G)) :
    (commutingSylow T L).conjBy a ⊓ embeddedCenter (T : Subgroup G) =
      zpowers (MulAut.conj a z) := by
  have hZ : (embeddedCenter (T : Subgroup G)).map (MulAut.conj a).toMonoidHom =
      embeddedCenter (T : Subgroup G) := by
    change (centerIn (T : Subgroup G)).map _ = centerIn (T : Subgroup G)
    have he : (T : Subgroup G).map (MulAut.conj a).toMonoidHom = (T : Subgroup G) :=
      mem_normalizer_iff_map_conj_eq.mp ha
    rw [centerIn_map_equiv, he]
  have he := congrArg (fun A : Subgroup G => A.map (MulAut.conj a).toMonoidHom)
    (commuting_inf_center h e d)
  rwa [map_inf _ _ _ (MulAut.conj a).injective, hZ, MonoidHom.map_zpowers] at he

/-- Distinct conjugate center lines force disjoint relatively normal two-subgroups.
This proves the source's disjointness in the present Sylow configuration. -/
theorem commuting_conjugates_disjoint (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    {a b : G} (ha : a ∈ normalizer (T : Set G))
    (hb : b ∈ normalizer (T : Set G))
    (hab : MulAut.conj a z ≠ MulAut.conj b z) :
    Disjoint ((commutingSylow T L).conjBy a) ((commutingSylow T L).conjBy b) := by
  apply disjoint_iff.mpr
  by_contra hn
  have hA := sylow_normalizes_component_and_commuting h |>.2
  have hnorm := (le_inf (conjugate_normal_in_sylow hA ha)
    (conjugate_normal_in_sylow hA hb)).trans inf_normalizer_le_normalizer_inf
  have hmeet := inf_centerIn_ne_bot T.isPGroup' hn
    (inf_le_left.trans (conjugate_le_sylow inf_le_left ha)) hnorm
  apply hmeet
  apply eq_bot_iff.mpr
  intro x hx
  have hxa : x ∈ zpowers (MulAut.conj a z) :=
    conjugate_commuting_inf_center h e d ha ▸ ⟨hx.1.1, hx.2⟩
  have hxb : x ∈ zpowers (MulAut.conj b z) :=
    conjugate_commuting_inf_center h e d hb ▸ ⟨hx.1.2, hx.2⟩
  rcases (mem_zpowers_two ((MulAut.conj a).orderOf_eq z |>.trans h.involution)).mp hxa with hx1 | hxa
  · exact hx1
  rcases (mem_zpowers_two ((MulAut.conj b).orderOf_eq z |>.trans h.involution)).mp hxb with hx1 | hxb
  · exact hx1
  exact (hab (hxa.symm.trans hxb)).elim

/-- The conjugate with central involution vz is faithful on L. -/
theorem fusion_conjugate_disjoint_commuting (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v) :
    Disjoint ((commutingSylow T L).conjBy f.second) (commutingSylow T L) := by
  have hne : MulAut.conj f.second z ≠ MulAut.conj 1 z := by
    rw [f.second_z]
    simp only [map_one, MulAut.one_apply]
    intro he
    exact ne_one_of_order_two d.v_order (mul_right_cancel (he.trans (one_mul z).symm))
  have hh := commuting_conjugates_disjoint h e d f.second_normalizes
    (normalizer (T : Set G)).one_mem hne
  rwa [conjBy_one] at hh

/-- The conjugate T_C^k is itself the R of a genuine intersection setup.
This makes the earlier 16.4.2 noncontainment and fixed-subgroup generation
arguments applicable to the exceptional pointwise centralizer. -/
theorem fusion_conjugate_setup (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v) :
    IntersectionSetup T z L f.second ((commutingSylow T L).conjBy f.second) := by
  let C := (commutingSylow T L).conjBy f.second
  let K := (centralizer (L : Set G)).conjBy f.second
  have hCT : C ≤ (T : Subgroup G) := conjugate_le_sylow inf_le_left f.second_normalizes
  have hCK : C ≤ K := map_mono inf_le_right
  have hCKN : C ≤ K ⊓ normalizer (centralizer (L : Set G) : Set G) :=
    le_inf hCK (hCT.trans (h.normalizers_eq ▸ h.sylow_normalizes))
  have haC : MulAut.conj f.second z ∈ C :=
    mem_map_of_mem _ h.toStandardSetup.z_mem_commutingSylow
  have ha2 : orderOf (MulAut.conj f.second z) = 2 :=
    (MulAut.conj f.second).orderOf_eq z |>.trans h.involution
  have hKne : K ≠ centralizer (L : Set G) := by
    intro he
    have haC0 : MulAut.conj f.second z ∈ commutingSylow T L :=
      ⟨hCT haC, he ▸ hCK haC⟩
    have ha1 : MulAut.conj f.second z = 1 := by
      have hh : MulAut.conj f.second z ∈ C ⊓ commutingSylow T L := ⟨haC, haC0⟩
      simpa only [C, (fusion_conjugate_disjoint_commuting h e d f).eq_bot, mem_bot] using hh
    exact ne_one_of_order_two ha2 ha1
  have hseven := h.toStandardSetup.commutingSylow_sylow.map (MulAut.conj f.second)
  have hCs : SylowIn C K := hseven
  refine ⟨h.toStandardSetup, ⟨⟨f.second, rfl⟩, hKne, ?_⟩, ?_, hCT⟩
  · let a : ↥(K ⊓ normalizer (centralizer (L : Set G) : Set G)) :=
      ⟨MulAut.conj f.second z, hCKN haC⟩
    have ha : orderOf a = 2 := (orderOf_coe a).symm.trans ha2
    exact even_iff_two_dvd.mpr (ha ▸ orderOf_dvd_natCard a)
  · exact SylowIn.of_maximal hCs.isPGroup hCKN
      (fun Q hp hQ hCQ => hCs.maximal hp (hQ.trans inf_le_left) hCQ)

/-- The normal intersection T_L ∩ T_C^k is trivial: its central involution
would be v, which already belongs to the disjoint conjugate T_C^h. -/
theorem component_inf_fusion_conjugate (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v) :
    componentSylow T L ⊓ (commutingSylow T L).conjBy f.second = ⊥ := by
  by_contra hn
  have hnorm := sylow_normalizes_component_and_commuting h
  have hmeet := inf_centerIn_ne_bot T.isPGroup' hn (inf_le_left.trans inf_le_left)
    ((le_inf hnorm.1 (conjugate_normal_in_sylow hnorm.2 f.second_normalizes)).trans
      inf_normalizer_le_normalizer_inf)
  apply hmeet
  apply eq_bot_iff.mpr
  intro x hx
  have hxv : x ∈ zpowers v := component_inf_center h hr d ▸ ⟨hx.1.1, hx.2⟩
  rcases (mem_zpowers_two d.v_order).mp hxv with hx1 | hxv
  · exact hx1
  rw [hxv] at hx ⊢
  have hvfirst : v ∈ (commutingSylow T L).conjBy f.first :=
    ⟨z, h.toStandardSetup.z_mem_commutingSylow, f.first_z⟩
  have hdis := commuting_conjugates_disjoint h e d f.first_normalizes f.second_normalizes
    (by rw [f.first_z, f.second_z]; intro he
        exact ne_one_of_order_two h.involution
          (mul_left_cancel ((mul_one v).trans he)).symm)
  exact hdis.eq_bot ▸ (show v ∈ (commutingSylow T L).conjBy f.first ⊓
    (commutingSylow T L).conjBy f.second from ⟨hvfirst, hx.1.2⟩)

/-- Relative normality and the trivial intersection give elementwise commutation. -/
theorem fusion_conjugate_centralizes_component (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v) :
    (commutingSylow T L).conjBy f.second ≤ centralizer (componentSylow T L : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  apply eq_bot_iff.mpr
  rw [← component_inf_fusion_conjugate h hr e d f]
  have hn := sylow_normalizes_component_and_commuting h
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp
      ((conjugate_le_sylow inf_le_left f.second_normalizes).trans hn.1))
    (le_normalizer_iff_commutator_le_right.mp
      (inf_le_left.trans (conjugate_normal_in_sylow hn.2 f.second_normalizes)))


/-- Conjugation by the actual Sylow subgroup, transported to PSL₂. -/
def sylowModelAction (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F) :
    (T : Subgroup G) →* MulAut (PSL2 F) :=
  (MulAut.congr e).toMonoidHom.comp
    (L.normalizerMonoidHom.comp (inclusion h.sylow_normalizes))

/-- The actual image of T_L in the projective carrier. -/
def componentModelSylow (T : Sylow 2 G) (L : Subgroup G) (e : L ≃* PSL2 F) :
    Subgroup (PSL2 F) := ((componentSylow T L).subgroupOf L).map e.toMonoidHom

/-- The genuine action of T_C^k, without replacing it by an abstract isomorphic group. -/
def fusionModelAction (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F)
    (f : FusionConjugators T z v) :
    (commutingSylow T L).conjBy f.second →* MulAut (PSL2 F) :=
  (sylowModelAction h e).comp
    (inclusion (conjugate_le_sylow inf_le_left f.second_normalizes))

theorem fusionModelAction_injective (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v) : Function.Injective (fusionModelAction h e f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have ha' : L.normalizerMonoidHom
      ⟨a, h.sylow_normalizes (conjugate_le_sylow inf_le_left f.second_normalizes a.property)⟩ = 1 :=
    (MulAut.congr e).injective (by
      change (MulAut.congr e) (L.normalizerMonoidHom _) = 1 at ha
      rw [map_one]
      convert ha using 1
      congr 2)
  have haK : (a : G) ∈ centralizer (L : Set G) := by
    change (⟨(a : G), h.sylow_normalizes
      (conjugate_le_sylow inf_le_left f.second_normalizes a.property)⟩ : normalizer (L : Set G)) ∈
      (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))
    rw [← normalizerMonoidHom_ker]
    exact ha'
  have ha1 : (a : G) = 1 := by
    have hm : (a : G) ∈ (commutingSylow T L).conjBy f.second ⊓ commutingSylow T L :=
      ⟨a.property, conjugate_le_sylow inf_le_left f.second_normalizes a.property, haK⟩
    simpa only [(fusion_conjugate_disjoint_commuting h e d f).eq_bot, mem_bot] using hm
  exact Subtype.ext ha1

/-- The faithful image fixes the whole actual component Sylow pointwise. -/
theorem fusionModelAction_fixes_component (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (e : L ≃* PSL2 F) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v)
    (a : (commutingSylow T L).conjBy f.second) (x : PSL2 F)
    (hx : x ∈ componentModelSylow T L e) : fusionModelAction h e f a x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  change e (L.normalizerMonoidHom _ (e.symm (e y))) = e y
  rw [e.symm_apply_apply]
  congr 1
  apply Subtype.ext
  change (a : G) * (y : G) * (a : G)⁻¹ = y
  have hc := fusion_conjugate_centralizes_component h hr e d f a.property y hy
  rw [← hc, mul_inv_cancel_right]

/-- The reflection already places v in the actual derived subgroup of T. -/
theorem marked_v_mem_derived (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (d : CentralizerGeometry T z L r v) :
    v ∈ ⁅(T : Subgroup G), (T : Subgroup G)⁆ := by
  obtain ⟨t, ht, htr⟩ := d.reflection
  have hvr : v * r = r * v :=
    mem_centralizer_singleton_iff.mp
      ((d.component_fixed.symm ▸ mem_zpowers v :
        v ∈ componentSylow T L ⊓ involutionCentralizer r).2)
  have he : ⁅t, r⁆ = v := by
    change MulAut.conj t r * r⁻¹ = v
    rw [htr, ← hvr, mul_inv_cancel_right]
  exact he ▸ commutator_mem_commutator ht.1.1 (h.le_sylow hr)

/-- Normalizer fusion transports v's derived membership back to z. -/
theorem fusion_z_mem_derived (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (d : CentralizerGeometry T z L r v)
    (f : FusionConjugators T z v) :
    z ∈ ⁅(T : Subgroup G), (T : Subgroup G)⁆ := by
  have hn : f.first ∈ normalizer ((⁅(T : Subgroup G), (T : Subgroup G)⁆ : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : (T : Subgroup G).map (MulAut.conj f.first).toMonoidHom = (T : Subgroup G) :=
      mem_normalizer_iff_map_conj_eq.mp f.first_normalizes
    change (⁅(T : Subgroup G), (T : Subgroup G)⁆).map (MulAut.conj f.first).toMonoidHom = _
    rw [map_commutator, he]
  apply (mem_normalizer_iff.mp hn z).mpr
  change MulAut.conj f.first z ∈ _
  rw [f.first_z]
  exact marked_v_mem_derived h hr d

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
