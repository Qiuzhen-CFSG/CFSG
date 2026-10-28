module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Terminal.Source
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Aligning the original natural diagonal

The actual SL₃(2) action is transitive on the nonzero vectors of each
moved factor when the fixed kernel vanishes. Crossed centralization makes
the two component actions independent, so the original component orbit
moves any diagonal with two nonzero coordinates to the T-central diagonal.
The alignment normalizes the first moved factor and preserves an active pair.
The terminal consumer is in Complete; no later survivor or w=2 is used.

Source: Aschbacher--Smith, 10.2.12, last paragraph on printed p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}


omit [Finite G] in
private theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a*b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
  Subgroup.conjBy_mul H a b

omit [Finite G] in
private theorem map_conj_commutator (H K : Subgroup G) (a : G) :
    (⁅H,K⁆).map (MulAut.conj a).toMonoidHom =
      ⁅H.map (MulAut.conj a).toMonoidHom,K.map (MulAut.conj a).toMonoidHom⁆ :=
  map_commutator H K (MulAut.conj a).toMonoidHom

omit [Finite G] in
private theorem conjugate_eq_of_mem_normalizer (H : Subgroup G) {a : G}
    (ha : a ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj a).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp ha

/-- The literal natural section is transitive on nonzero moved vectors. -/
theorem natural_moved_transitive
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {u v : G} (hu : u ∈ ⁅D.fullModule,L⁆) (hv : v ∈ ⁅D.fullModule,L⁆)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ a ∈ L, (MulAut.conj a) u = v := by
  have hk := moved_fixed_eq_bot_of_full_fixed_eq_bot m hn hz
  have hi : Function.Injective m.natural.coordinates := by
    apply m.natural.coordinates.ker_eq_bot_iff.mp
    rw [m.natural.kernel_eq,hk]
    simp
  have hu0 : (m.natural.coordinates ⟨u,hu⟩).toAdd ≠ 0 := by
    intro he
    have hh := (m.natural.coordinates_eq_one_iff ⟨u,hu⟩).mp he
    rw [hk] at hh
    exact hu1 (mem_bot.mp hh)
  have hv0 : (m.natural.coordinates ⟨v,hv⟩).toAdd ≠ 0 := by
    intro he
    have hh := (m.natural.coordinates_eq_one_iff ⟨v,hv⟩).mp he
    rw [hk] at hh
    exact hv1 (mem_bot.mp hh)
  obtain ⟨s,hs⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (m.natural.coordinates ⟨u,hu⟩).toAdd (m.natural.coordinates ⟨v,hv⟩).toAdd hu0 hv0
  obtain ⟨a,ha⟩ := (m.quotient.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) s
  refine ⟨a,a.property,?_⟩
  have he := m.natural.equivariant a ⟨u,hu⟩
  change _ = (m.quotient (QuotientGroup.mk' (pCore 2 L) a)).val *ᵥ
    (m.natural.coordinates ⟨u,hu⟩).toAdd at he
  have heq := congrArg (fun q : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
    q.val *ᵥ (m.natural.coordinates ⟨u,hu⟩).toAdd) ha
  exact congrArg Subtype.val (hi (Multiplicative.toAdd.injective
    (he.trans (heq.trans hs))))

/-- Independent component actions align the two nonzero diagonal coordinates. -/
theorem natural_diagonal_transitive
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {u v u' v' : G}
    (hu : u ∈ ⁅D.fullModule,L⁆) (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hu' : u' ∈ ⁅D.fullModule,L⁆) (hv' : v' ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hu1' : u' ≠ 1) (hv1' : v' ≠ 1) :
    ∃ a ∈ localOrbit T L, a ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
      (MulAut.conj a) (u*v) = u'*v' := by
  let W := ⁅D.fullModule,L⁆
  let B := W.map (MulAut.conj t).toMonoidHom
  have hLC : L ≤ centralizer (B : Set G) := le_centralizer_iff.mp (m.crossed t ht htn)
  have hKC : L.map (MulAut.conj t).toMonoidHom ≤ centralizer (W : Set G) := by
    have htn' : t⁻¹ ∉ normalizer (L : Set G) := by simpa only [inv_mem_iff] using htn
    have h := map_mono (f := (MulAut.conj t).toMonoidHom)
      (le_centralizer_iff.mp (m.crossed t⁻¹ ((T : Subgroup G).inv_mem ht) htn'))
    rw [Theory.Quasithin.map_centralizer,←map_conj_mul,mul_inv_cancel] at h
    simpa using h
  obtain ⟨a,ha,hua⟩ := natural_moved_transitive m hn hz hu hu' hu1 hu1'
  obtain ⟨w,hw,rfl⟩ := hv
  obtain ⟨w',hw',rfl⟩ := hv'
  have hw1 : w ≠ 1 := by intro he; apply hv1; simp only [he,map_one]
  have hw1' : w' ≠ 1 := by intro he; apply hv1'; simp only [he,map_one]
  obtain ⟨b,hb,hwb⟩ := natural_moved_transitive m hn hz hw hw' hw1 hw1'
  let k := (MulAut.conj t) b
  have hk : k ∈ L.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ hb
  have hkR : k ∈ localOrbit T L := by
    have he := componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn
    change k ∈ componentOrbit L (T : Subgroup G)
    rw [he]
    exact (le_sup_right : L.map (MulAut.conj t).toMonoidHom ≤ _) hk
  have hku : (MulAut.conj k) u = u := by
    change k*u*k⁻¹=u
    rw [←hKC hk u hu,mul_inv_cancel_right]
  have hav : (MulAut.conj a) ((MulAut.conj t) w') = (MulAut.conj t) w' := by
    change a*((MulAut.conj t) w')*a⁻¹ = _
    have hc : ((MulAut.conj t) w') * a = a * ((MulAut.conj t) w') :=
      hLC ha _ (mem_map_of_mem _ hw')
    rw [←hc,mul_inv_cancel_right]
  have hkv : (MulAut.conj k) ((MulAut.conj t) w) = (MulAut.conj t) w' := by
    have he : (MulAut.conj t) (b*w*b⁻¹) = (MulAut.conj t) w' :=
      congrArg (MulAut.conj t) hwb
    change k * ((MulAut.conj t) w) * k⁻¹ = _
    simpa only [map_mul,map_inv] using he
  refine ⟨a*k,(localOrbit T L).mul_mem (le_componentOrbit L T ha) hkR,
    (normalizer (W : Set G)).mul_mem (m.natural.normalized ha)
      ((Subgroup.centralizer_le_normalizer _) (hKC hk)),?_⟩
  change (MulAut.conj (a*k)) (u * (MulAut.conj t) w) = u' * (MulAut.conj t) w'
  rw [show MulAut.conj (a*k) = MulAut.conj a * MulAut.conj k from map_mul _ _ _,
    MulAut.mul_apply, map_mul,hku,hkv,map_mul,hua,hav]

theorem terminalWitness_of_active_pair_common_diagonal
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {u v : G} (hu : u ∈ ⁅D.fullModule,L⁆)
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u*v ∈ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    Nonempty (TerminalWitness T D g) := by
  obtain ⟨u',v',hu',hv',hu1',hv1',huf,hvf,hzT,hzorder⟩ :=
    exists_natural_diagonal m c.nonnormal ht htn hz
  obtain ⟨a,ha,haW,he⟩ := natural_diagonal_transitive m c.nonnormal hz ht htn
    hu hv hu' hv' hu1 hv1 hu1' hv1'
  have haM := (localOrbit T L).le_normalizer ha
  have heW := conjugate_eq_of_mem_normalizer _ haW
  have hact : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj (a*g)).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro hh
    apply hactive
    apply (map_le_map_iff_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective).mp
    rw [Theory.Quasithin.map_centralizer,heW,←map_conj_mul]
    exact hh
  have hcommon : u'*v' ∈ D.fullModule ⊓
      D.fullModule.map (MulAut.conj (a*g)).toMonoidHom := by
    constructor
    · have hgen := source_nonnormal_fullModule_eq_moved_pair D c.nonnormal ht
        (m.crossed t ht htn)
      rw [hgen]
      exact mul_mem_sup hu' hv'
    · rw [map_conj_mul,←he]
      exact mem_map_of_mem _ huv
  apply terminalWitness_of_common_central_point c m hsmall hz hti
    a t (a*g) (u'*v') haM ht htn (Or.inl rfl) hact hcommon hzT.2
  intro heq
  rw [heq,orderOf_one] at hzorder
  norm_num at hzorder

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
