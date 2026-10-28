module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.HallOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Attainment

/-!
# Generation one in the exceptional equal-component row

The original conjugation action is transported through the chosen G₂ marking
to its actual binary natural normalizer. Transitivity aligns the source point
with the first vector; the literal residual maps onto the genuine point fixer,
and its two-core maps into the model two-core. The model calculation and the
proved Hall-order coprimality make the Hall actor trivial on the natural
quotient. Fixed-space vanishing, derived from the preceding source geometry,
lifts this to the original seed. Hall faithfulness contradicts n(H)>1.

The exact OddKernelNormalizer input remains with
qt-d-1222-natural-odd-kernel-normalizer. Earlier geometry, 11.3.2, the
linear fixed-space input and Kz=K retain qt-d-1222-natural-local-geometry,
qt-d-1222-shadow-linear-geometry, qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison, with final discharge by
qt-d-1222-shadow-components. The strict-component and smaller-carrier
generation arguments remain with qt-d-1222-shadow-component-witness.
Source: Aschbacher--Smith, 11.4.4, printed p.778 of refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
open LocalGeometry Atlas.G2 Atlas.G2.LieParabolicSetup Natural.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (.g2 m))
attribute [local instance] ZMod.algebra

private theorem point_image (z : V)
    (hz : ((Coordinates.g2 m).projection z).toAdd ∈ f.space 0)
    (hz0 : ((Coordinates.g2 m).projection z).toAdd ≠ 0) :
    ((f.Li 0).subgroupOf L).map (Coordinates.g2 m).quotientMap =
      G2Action.pointFixer ((Coordinates.g2 m).projection z).toAdd := by
  let c := Coordinates.g2 m
  let w := (c.projection z).toAdd
  change ((f.Li 0).subgroupOf L).map c.quotientMap = G2Action.pointFixer w
  have hlarge : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2:ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  apply le_antisymm
  · rintro x ⟨l,hl,rfl⟩
    have hh := Closure.Nonabelian.PointModels.model_residual_fixes_line c
      (f.space 0) (f.dimension 0) w hz hz0
      (c.residualProjection (f.space 0) ⟨l,hl⟩)
    rw [c.residualProjection_coe] at hh
    exact hh
  · change G2Action.pointFixer w ≤
      ((localResidual L (c.preimage (f.space 0))).subgroupOf L).map c.quotientMap
    rw [Closure.Nonabelian.PointModels.model_residual_image]
    let := G2Action.pointFixer_perfect hlarge hz0
    apply le_map_solvableResidual_of_isPerfect
    apply le_subspaceStabilizer
    intro a ha v hv
    change Natural.action S.field.Carrier a v ∈ f.space 0
    rw [eq_span_singleton_of_mem_of_finrank_eq_one (f.dimension 0) hz hz0] at hv ⊢
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,show Natural.action S.field.Carrier a w=w from ha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp only [Set.mem_singleton_iff]; rfl))

private theorem map_core_le {A B : Type*} [Group A] [Group B]
    (q : A →* B) (P : Subgroup A) : (P.pCoreIn 2).map q ≤ (P.map q).pCoreIn 2 := by
  let j := q.subgroupMap P
  have hn : ((pCore 2 P).map j).Normal := Normal.map inferInstance j (q.subgroupMap_surjective P)
  have h : (pCore 2 P).map j ≤ pCore 2 (P.map q) := le_sSup ⟨hn,pCore_isPGroup.map j⟩
  have hh := map_mono (f := (P.map q).subtype) h
  change ((pCore 2 P).map j).map (P.map q).subtype ≤ (P.map q).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 P).map (q.comp P.subtype) ≤ _ at hh
  change ((pCore 2 P).map P.subtype).map q ≤ _
  rw [Subgroup.map_map]
  exact hh

/-- The literal exceptional Hall action is trivial on the original seed. -/
theorem ofFlag_g2_odd_section_centralizes
    (z : V) (hz : ((Coordinates.g2 m).projection z).toAdd ∈ f.space 0)
    (hz0 : ((Coordinates.g2 m).projection z).toAdd ≠ 0)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (B : Subgroup G) (ho : Odd (Nat.card B))
    (hBV : B ≤ normalizer (V : Set G)) (hBz : B ≤ centralizer ({(z : G)} : Set G))
    (hc : ⁅B,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2)
    (hco : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1)) :
    B ≤ centralizer (V : Set G) := by
  let c := Coordinates.g2 m
  let F := S.field.Carrier
  let N := normalizer (V : Set G)
  let K := L.subgroupOf N
  let : K.Normal := normal_subgroupOf_of_le_normalizer (WeakClosure.seed_normalizer_le D S)
  let e : K ≃* L := subgroupOfEquivOfLe D.normalizes
  let η := c.quotientMap.comp e.toMonoidHom
  have hη : Function.Surjective η := c.quotientMap_surjective.comp e.surjective
  let α := c.conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let ρ : Representation (ZMod 2) N (Natural.Space F) :=
    { toFun a := AddMonoidHom.toZModLinearMap 2
        (M := Natural.Space F) (M₁ := Natural.Space F) (α a).toAddMonoidHom
      map_one' := LinearMap.ext (fun v => by
        change α 1 v = v
        rw [map_one]
        rfl)
      map_mul' a b := LinearMap.ext (fun v => by
        change α (a*b) v = α a (α b v)
        rw [map_mul]
        rfl) }
  have hnat (k : K) (w : Natural.Space F) : ρ k w = binary F (η k) w := by
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    have hw : (c.projection v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [←hw,binary_apply]
    change c.conjugationAction _ _ _ _ = _
    rw [c.conjugationAction_projection]
    exact c.projection_component_conjugation (e k) v
  have himage : actionImage (ρ.comp K.subtype) = actionImage (binary F) := by
    ext a
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨η k,Units.ext (LinearMap.ext (fun w => (hnat k w).symm))⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨k,rfl⟩ := hη x
      exact ⟨k,Units.ext (LinearMap.ext (hnat k))⟩
  let Q₀ : N →* linearNormalizer (binary F) :=
    ρ.asGroupHom.codRestrict _ (fun a => by
      change ρ.asGroupHom a ∈ normalizer (actionImage (binary F) : Set _)
      rw [←himage]
      exact actionImage_le_linearNormalizer ρ K ⟨a,rfl⟩)
  have hQ₀ (l : L) :
      (Q₀ (inclusion D.normalizes l)).val = (binary F).asGroupHom (c.quotientMap l) := by
    exact Units.ext (LinearMap.ext (hnat (e.symm l)))
  let w := (c.projection z).toAdd
  let v₀ := Natural.mk F (G2Action.firstVector (F := F))
  obtain ⟨g,hg⟩ := Natural.action_transitive (G2Action.first_ne_zero (F := F)) hz0
  change Natural.action F g v₀ = w at hg
  let t := normalizerEmbedding (binary F) g⁻¹
  let Q := (MulAut.conj t).toMonoidHom.comp Q₀
  let q := (linearNormalizer (binary F)).subtype.comp Q
  let r := (MulAut.conj g⁻¹).toMonoidHom.comp c.quotientMap
  have hq (l : L) : q (inclusion D.normalizes l) = (binary F).asGroupHom (r l) := by
    change (binary F).asGroupHom g⁻¹ * (Q₀ (inclusion D.normalizes l)).val *
      ((binary F).asGroupHom g⁻¹)⁻¹ = (binary F).asGroupHom (g⁻¹*(show Model F from c.quotientMap l)*(g⁻¹)⁻¹)
    simp only [hQ₀,map_mul,map_inv,inv_inv]
  have himageR : ((f.Li 0).subgroupOf L).map r = local₂ := by
    change ((f.Li 0).subgroupOf L).map
      ((MulAut.conj g⁻¹).toMonoidHom.comp c.quotientMap) = _
    rw [←Subgroup.map_map,point_image S m f z hz hz0,G2Action.pointFixer_map]
    change G2Action.pointFixer (Natural.action F g⁻¹ w) = _
    rw [←hg,Representation.inv_self_apply,G2Action.first_pointFixer]
  let P := (f.Li 0).subgroupOf N
  have hAL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hAN : f.Li 0 ≤ N := hAL.trans D.normalizes
  have hPQ : P.map q = local₂.map (binary F).asGroupHom := by
    rw [←himageR,Subgroup.map_map]
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hAL hx⟩,hx,(hq ⟨x,hAL hx⟩).symm⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨inclusion D.normalizes l,hl,hq l⟩
  have hσinj : Function.Injective (binary F).asGroupHom :=
    fun _ _ he => binary_faithful F (congrArg Units.val he)
  have hcore : (((f.Li 0).pCoreIn 2).subgroupOf N).map q ≤
      ((local₂ (F := F)).pCoreIn 2).map (binary F).asGroupHom := by
    rw [←pCoreIn_subgroupOf 2 (f.Li 0) N hAN]
    have hh := map_core_le q P
    rw [hPQ,←map_pCoreIn_of_injective 2 _ _ hσinj] at hh
    exact hh
  have hlarge : 2 < Nat.card F := by
    rw [S.field.card_eq]
    exact (show (2:ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  intro b hb
  let b' : N := ⟨b,hBV hb⟩
  have hpow : Q b' ^ Nat.card B = 1 := by
    rw [←map_pow]
    have hbpow : b ^ Nat.card B = 1 :=
      congrArg (fun x : B => (x : G)) (pow_card_eq_one' (x := (⟨b,hb⟩ : B)))
    rw [show b' ^ Nat.card B = 1 from Subtype.ext hbpow,map_one]
  have hfix : (Q b').val.val v₀ = v₀ := by
    change ((binary F).asGroupHom g⁻¹).val
      (ρ b' ((((binary F).asGroupHom g⁻¹)⁻¹).val v₀)) = v₀
    rw [←map_inv,inv_inv]
    change binary F g⁻¹ (ρ b' (binary F g v₀)) = v₀
    rw [binary_apply,binary_apply]
    change Natural.action F g⁻¹ (ρ b' (Natural.action F g v₀)) = v₀
    rw [hg]
    change Natural.action F g⁻¹ (c.conjugationAction _ _ b' (c.projection z).toAdd) = _
    rw [c.conjugationAction_projection]
    have hzb : V.normalizerMonoidHom b' z = z := Subtype.ext
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hBz hb)))
    calc
      _ = Natural.action F g⁻¹ w :=
        congrArg (fun v : V => Natural.action F g⁻¹ (c.projection v).toAdd) hzb
      _ = v₀ := by rw [←hg,Representation.inv_self_apply]
  have hcomm : ∀ x ∈ local₂ (F := F),
      normalizerAutomorphism F (Q b') x / x ∈ (local₂ (F := F)).pCoreIn 2 := by
    intro x hx
    apply (mem_map_iff_mem hσinj).mp
    have hact : (binary F).asGroupHom (normalizerAutomorphism F (Q b') x / x) =
        ⁅q b',(binary F).asGroupHom x⁆ := by
      rw [map_div]
      congr 1
      apply Units.ext
      apply LinearMap.ext
      intro v
      have hh := normalizerAutomorphism_intertwines F (Q b') x ((Q b').val⁻¹.val v)
      have hcanc : (Q b').val.val ((Q b').val⁻¹.val v) = v := by
        change ((Q b').val*(Q b').val⁻¹).val v=v
        rw [mul_inv_cancel]
        rfl
      rw [hcanc] at hh
      change binary F (normalizerAutomorphism F (Q b') x) v =
        (Q b').val.val (binary F x ((Q b').val⁻¹.val v))
      rw [binary_apply,binary_apply]
      exact hh.symm
    rw [hact]
    obtain ⟨y,hy,he⟩ := hPQ.ge (mem_map_of_mem (binary F).asGroupHom hx)
    rw [←he,←map_commutatorElement]
    exact hcore (mem_map_of_mem q (show ⁅b',y⁆ ∈ ((f.Li 0).pCoreIn 2).subgroupOf N from
      hc (commutator_mem_commutator hb hy)))
  have hb1 : Q b'=1 := G2Action.odd_coprime_point_section_eq_one hlarge
    (Q b') ho (S.field.card_eq.symm ▸ hco) hpow hfix hcomm
  have hρ : ρ.asGroupHom b' = 1 := by
    have hh := (MulAut.conj t).injective (hb1.trans (map_one _).symm)
    exact congrArg Subtype.val hh
  intro v hv
  let v' : V := ⟨v,hv⟩
  have hh := c.conjugationAction_projection (WeakClosure.seed_normalizer_le D S) le_rfl b' v'
  have hid : c.conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl b' (c.projection v').toAdd =
      (c.projection v').toAdd := by
    exact congrArg (fun u : (Module.End (ZMod 2) (Natural.Space F))ˣ =>
      u.val (c.projection v').toAdd) hρ
  have hvv : V.normalizerMonoidHom b' v' = v' :=
    Closure.Nonabelian.PointModels.projection_injective c hf
      (Multiplicative.toAdd.injective (hh.symm.trans hid))
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hvv)).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (.g2 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Source 11.4.4 for every outside H in the original exceptional equality row.
The earlier geometry and independently owned Hall-faithfulness input remain explicit. -/
theorem ofFlag_g2_equal_generation_eq_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) : ChapterE.generationParameter H = 1 := by
  apply Nat.le_antisymm ?_ (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change ChapterE.generationParameter H ≤ 1
  by_contra! hn
  obtain ⟨hP,n,_,hb,d,_,_,hY,hfaith,hBV,hcop⟩ :=
    ofFlag_g2_equal_faithful_hall_order S m f X z H h he hK hlinear h1132 hcontrol hH hHz hn
  have hc : ⁅d.witness.abelianGroup.map H.subtype,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2 := by
    have hc := commutator_le.mpr (fun b hb k hk =>
      Closure.coreQuotientCentralizer_commutator (hY hb).2 hk)
    simpa only [hK,ofFlag_firstResidual] using hc
  let E := ofFlag S f X z H
  let c := LocalGeometry.Coordinates.g2 m
  let v : V := ⟨z,E.V₁_le h.point_mem⟩
  have hf := (fixed_and_transitive D S E.point hlinear h1132).1
  have hv0 : (c.projection v).toAdd ≠ 0 := by
    intro hz0
    have hv1 : v=1 := Closure.Nonabelian.PointModels.projection_injective c hf
      (hz0.trans (map_one c.projection).symm)
    exact h.point_ne_one (congrArg Subtype.val hv1)
  have hfix := ofFlag_g2_odd_section_centralizes S m f v
    ((c.mem_preimage _ v).mp h.point_mem) hv0 hf _
    (d.witness.odd.of_dvd_nat (card_map_dvd _ _)) hBV
    (hY.trans inf_le_left) hc hcop
  have hz : d.witness.abelianGroup.map H.subtype = ⊥ := by
    rwa [inf_eq_left.mpr hfix] at hfaith
  have hB : d.witness.abelianGroup = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hz
  have hC : d.witness.cyclicGroup = ⊥ := bot_unique (d.witness.cyclic_le.trans hB.le)
  have hc1 := d.witness.card
  rw [Subgroup.card_eq_one.mpr hC] at hc1
  have hn2 : 2 ≤ n := by omega
  have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2
  omega

/-- The original selected H has generation one, with both residual alternatives
still interpreted as O²(H). The preceding geometry is retained verbatim. -/
theorem ofFlag_g2_equal_selected_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  obtain ⟨J,hJ,hJz,hs,_⟩ := ofFlag_equal_selected_radical_carrier S f X z H h he hK hNT h1132
  exact ⟨J,hJ,hJz,hs,ofFlag_g2_equal_generation_eq_one S m f X z J
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩ he hK hlinear h1132 hcontrol hJ hJz⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
