module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceSeedLines

/-!
# A common point in the actual commutator pencil

The derived pencil centralizer has order four. Its nonidentity moved spaces
are geometric lines; the point residual acts transitively on those lines,
so every line occurs. Lift this assertion through the same critical actor
and the original section coordinates. Two distinct pencil lines share a
nonzero point vector. Injectivity on the partner intersection identifies
its two ambient lifts, giving a common subgroup of order two.

This subgroup lies in an actual seed conjugate by the preceding seed-line
identification. Full natural L-action identifies it with a conjugate of
V₁. Thus it is a genuine denominator for the final quotient geometry, not
an independently selected model point.

Source: Aschbacher--Smith, 14.7.55(4),(6), 14.7.62 and formulas (a),(b),
printed pp.1066,1068--1069. Existing model conventions retain the attribution
in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion G2Exclusion.MarkedGeometry G2Exclusion.MarkedGeometry.MarkedPencil
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

private theorem model_moved_conjugate (m : BinaryG2Module)
    (g b : Atlas.G2.Model (ZMod 2)) :
    (subspaceCommutator m.action ⊤ (zpowers b)).map (m.action g) =
      subspaceCommutator m.action ⊤ (zpowers (g*b*g⁻¹)) := by
  have he : ∀ a v, m.action a (m.action g⁻¹ v) =
      m.action g⁻¹ (m.action ((MulAut.conj g) a) v) := by
    intro a v
    change m.action a (m.action g⁻¹ v) = m.action g⁻¹ (m.action (g*a*g⁻¹) v)
    simp only [map_mul,Module.End.mul_apply,m.action.inv_self_apply]
  have hh := subspaceCommutator_map_embedding m.action m.action (MulAut.conj g).toMonoidHom
    (m.action g⁻¹) he (zpowers b) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr (m.action.apply_bijective g⁻¹).surjective,
    MonoidHom.map_zpowers] at hh
  rw [hh,←Submodule.map_comp]
  have hc : (m.action g).comp (m.action g⁻¹) = LinearMap.id := by
    ext v
    exact m.action.self_inv_apply g v
  rw [hc,Submodule.map_id]
  rfl

/-- Every line of the marked pencil is the moved space of an actual
nonidentity member of the derived pencil centralizer. -/
theorem model_pencil_line_commutator (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) (l : ZeroProductLine (ZMod 2))
    (hl : pointOnLine p l) :
    ∃ b ∈ derivedCentralizer m.singularMap m.action p, b ≠ 1 ∧
      subspaceCommutator m.action ⊤ (zpowers b) = m.singularMap.line l := by
  have hcard := (derivedCentralizer_structure m.singularMap m.action m.equivariant p).2
  have hbot : derivedCentralizer m.singularMap m.action p ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at hcard
    omega
  obtain ⟨b,hb,hbn⟩ := (bot_or_exists_ne_one _).resolve_left hbot
  obtain ⟨l₀,hl₀,he⟩ := model_nonidentity_moved m p b hb hbn
  obtain ⟨g,hg,hgl⟩ := pencil_transitive ⊤ le_top p l₀ l hl₀ hl
  have hgp : g • p = p := by
    obtain ⟨a,_,rfl⟩ := hg
    exact a.property.1
  have hmem := mem_map_of_mem (MulAut.conj g).toMonoidHom hb
  rw [derivedCentralizer_conjugate m.singularMap m.action m.equivariant,hgp] at hmem
  refine ⟨g*b*g⁻¹,hmem,?_,?_⟩
  · intro hh
    apply hbn
    apply (MulAut.conj g).injective
    simpa using hh
  · rw [←model_moved_conjugate,he,
      ←m.singularMap.line_equivariant m.action m.equivariant,hgl]

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

/-- Every marked pencil line lifts to a member of the literal ambient
commutator family of the same critical actor. -/
theorem source_pencil_line_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map f = fullCentralizer m.singularMap m.action p)
    (l : ZeroProductLine (ZMod 2)) (hl : pointOnLine p l) :
    ∃ b ∈ derivedActorLift (f.comp (starMap F)) path.Uα,
      ⁅F.U,zpowers b⁆ ≠ ⊥ ∧ ⁅F.U,zpowers b⁆ ≤ F.U ∧ ⁅F.U,zpowers b⁆ ≤ path.Uα ∧
      c.imageSpace ⁅F.U,zpowers b⁆ = (m.singularMap.line l).map E.toLinearMap := by
  obtain ⟨b,hb,_,hmove⟩ := model_pencil_line_commutator m p l hl
  have hθ : (path.Uα.subgroupOf F.H).map (f.comp (starMap F)) =
      fullCentralizer m.singularMap m.action p := by rw [←map_map]; exact hA
  have hB := derivedActorLift_image (f.comp (starMap F)) m p path.Uα hθ
  obtain ⟨a,ha,hea⟩ := hB.symm ▸ hb
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hcyc := zpowers_le.mpr (derivedActorLift_le _ _ ha)
  have hCU : ⁅F.U,zpowers (a:G)⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((hcyc.trans hAH).trans c.normalized)
  have hi : c.imageSpace ⁅F.U,zpowers (a:G)⁆ = (m.singularMap.line l).map E.toLinearMap := by
    rw [commutator_comm,c.imageSpace_commutator _ _ ((zpowers_le.mpr a.property)) le_rfl,
      imageSpace_U c]
    rw [cyclic_commutator_model_image m E (f.comp (starMap F))
      (fun a v => he (starMap F a) v) a,hea,hmove]
  refine ⟨a,ha,?_,hCU,
    (commutator_mono le_rfl hcyc).trans
      (le_normalizer_iff_commutator_le_right.mp (normalizes_partner h path)),hi⟩
  intro hz
  have hzero : (m.singularMap.line l).map E.toLinearMap = ⊥ := by
    rw [←hi,hz]
    simp [BinaryConjugationSection.imageSpace]
  have hline : m.singularMap.line l = ⊥ :=
    (Submodule.map_injective_of_injective E.injective) (by simpa using hzero)
  have hc := m.singularMap.line_card l
  rw [hline] at hc
  simp at hc



/-- An order-two subgroup of any seed conjugate is a conjugate of the
original flag point, using the full natural action of L. -/
private theorem seed_point_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (N : Subgroup G) (hN : Nat.card N = 2)
    (a : G) (hNa : N ≤ conjugate V a) :
    ∃ g : G, N = conjugate (F.Vi 1) g := by
  have hn : N ≠ ⊥ := by intro hh; rw [hh,card_bot] at hN; omega
  obtain ⟨x,hx,hxn⟩ := (bot_or_exists_ne_one N).resolve_left hn
  have hgen := zpowers_eq_top_of_prime_card hN
    (g := (⟨x,hx⟩ : N)) (fun hh => hxn (congrArg Subtype.val hh))
  have hNx : N = zpowers x := by
    have hh := congrArg (Subgroup.map N.subtype) hgen
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  obtain ⟨y,hy,hyx⟩ := hNa hx
  have hyn : y ≠ 1 := by intro he; subst y; exact hxn (by simpa using hyx.symm)
  obtain ⟨z,hzn,hzg⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzV : z ∈ V := F.le_seed 1 (hzg.symm ▸ mem_zpowers z)
  obtain ⟨l,_,hly,_⟩ := vector_interchange h hzV hy hzn hyn
  refine ⟨l⁻¹*a,?_⟩
  rw [hNx,hzg]
  change zpowers x = (zpowers z).map (MulAut.conj (l⁻¹*a)⁻¹).toMonoidHom
  rw [MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at hyx
  change a⁻¹*y*a = x at hyx
  calc
    x = a⁻¹*y*a := hyx.symm
    _ = a⁻¹*(l*z*l⁻¹)*a := by rw [hly]
    _ = (l⁻¹*a)⁻¹*z*(l⁻¹*a) := by group

include c in
/-- Two distinct members of the actual commutator pencil share an
order-two subgroup. The family and its literal ambient lifts are retained. -/
theorem source_pencil_common_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Bijective f)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map f = fullCentralizer m.singularMap m.action p)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα) :
    ∃ N R S : Subgroup G, Nat.card N = 2 ∧ N ≤ R ∧ N ≤ S ∧ R ≠ S ∧
      (R ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (f.comp (starMap F)) path.Uα, R = ⁅F.U,zpowers b⁆) ∧
      (S ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (f.comp (starMap F)) path.Uα, S = ⁅F.U,zpowers b⁆) ∧
      ∃ g : G, N = conjugate (F.Vi 1) g := by
  let : Finite {l : ZeroProductLine (ZMod 2) // pointOnLine p l} :=
    Nat.finite_of_card_ne_zero (by rw [pencil_card]; decide)
  let : Nontrivial {l : ZeroProductLine (ZMod 2) // pointOnLine p l} :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [pencil_card]; decide)
  obtain ⟨l,l',hne⟩ := exists_pair_ne {l : ZeroProductLine (ZMod 2) // pointOnLine p l}
  obtain ⟨b,hb,hbn,hbU,hbA,hbi⟩ := source_pencil_line_commutator c h path hplace f m E he p hA l l.property
  obtain ⟨d,hd,hdn,hdU,hdA,hdi⟩ := source_pencil_line_commutator c h path hplace f m E he p hA l' l'.property
  have hdistinct : ⁅F.U,zpowers b⁆ ≠ ⁅F.U,zpowers d⁆ := by
    intro hh
    apply hne
    apply Subtype.ext
    apply m.singularMap.line_injective
    apply Submodule.map_injective_of_injective E.injective
    rw [←hbi,←hdi,hh]
  have hpne : m.singularMap.point p ≠ ⊥ := by
    intro hz
    have hc := m.singularMap.point_card p
    rw [hz] at hc
    simp at hc
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hvb : E v ∈ c.imageSpace ⁅F.U,zpowers b⁆ := by
    rw [hbi]
    exact ⟨v,(m.singularMap.incidence p l).mp l.property hv,rfl⟩
  have hvd : E v ∈ c.imageSpace ⁅F.U,zpowers d⁆ := by
    rw [hdi]
    exact ⟨v,(m.singularMap.incidence p l').mp l'.property hv,rfl⟩
  obtain ⟨x,hx,hxe⟩ := (c.mem_imageSpace_iff _ _).mp hvb
  obtain ⟨y,hy,hye⟩ := (c.mem_imageSpace_iff _ _).mp hvd
  have hxy : x = y := coordinates_injective_on_partner c path.Uα hpoint (hbA hx) (hdA hy)
    (Multiplicative.toAdd.injective (hxe.trans hye.symm))
  have hxcard : Nat.card (zpowers (x:G)) = 2 := by
    rw [←imageSpace_card c path.Uα _ hpoint (zpowers_le.mpr x.property)
      (zpowers_le.mpr (hbA hx)),imageSpace_zpowers c x,hxe,
      Module.natCard_eq_pow_finrank (K := ZMod 2),finrank_span_singleton (by simpa using hvn)]
    simp
  obtain ⟨a,ha⟩ := source_commutator_seed_conjugate c h path hplace f hf m E he p hA hpoint b hb hbn
  have hseed : zpowers (x:G) ≤ conjugate V a := ha ▸ ((zpowers_le.mpr hx).trans le_sup_left)
  exact ⟨zpowers (x:G),⁅F.U,zpowers b⁆,⁅F.U,zpowers d⁆,hxcard,
    zpowers_le.mpr hx,zpowers_le.mpr (hxy ▸ hy),hdistinct,
    ⟨hbn,b,hb,rfl⟩,⟨hdn,d,hd,rfl⟩,seed_point_conjugate h _ hxcard a hseed⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
