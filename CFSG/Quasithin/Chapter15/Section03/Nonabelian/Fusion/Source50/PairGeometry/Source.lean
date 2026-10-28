module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source50Model.Determinant
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Preamble.ReducedAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Transport
public import CFSG.Quasithin.ChapterF.Section09.Basic

/-!
# The actual source54 pair and its quadratic marking

The ordinary C_Y(V) identity makes the kernel of the actual YT-action a
2-group. Its faithful quotient identifies the literal source star with the
orthogonal actor. The source53 movement hyperplane then transports through
the determinant model to construct G.2.6. Residual spanning chooses g in Y
whose conjugate point is not perpendicular to Z. The original F.9 closure
supplies the ambient G.2.1 data after replacing ZS by this hyperplane.

The actual source54 consumer constructs the pair generation, core product,
central natural module, elementary-four intersection, and common-multiplicity
natural layers. The determinant equation is retained for the later singular
and perpendicular assertions. Earlier source48–53 inputs remain explicit;
the original source50 assembly supplies them from its standing hypotheses.

Source: Aschbacher–Smith, 15.3.48–54, printed pp.1145–1146, and G.2.6,
printed p.336. The constructions use the original ambient subgroups.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
open FusionCore.CosetSetup.Preamble
open CFSG.Quasithin.ChapterG.Section02
open OrthogonalPlusFour

variable {G : Type*} [Group G] [Finite G]

/-- In the ordinary branch the actual YT-action has a two-group kernel.
Restricting its kernel to YT/Y leaves the already identified C_Y(V). -/
theorem ordinary_kernel_isPGroup (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G)) :
    IsPGroup 2 (restrictedActor d.action (d.Y ⊔ (d.T : Subgroup G))
      (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le)).ker := by
  let K : Subgroup G := d.Y ⊔ (d.T : Subgroup G)
  let N : Subgroup K := d.Y.subgroupOf K
  have hY : K ≤ normalizer (d.Y : Set G) := sup_le d.Y.le_normalizer
    (residualY_normalized d.M d.Mc d.T d.sylow_le)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hY
  have hgen : N ⊔ (d.T : Subgroup G).subgroupOf K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (K ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N _ d.T.isPGroup'.comap_subtype hgen
  let f : K →* OrthogonalActor := restrictedActor d.action K
    (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le)
  let r : f.ker →* K ⧸ N := (QuotientGroup.mk' N).comp f.ker.subtype
  have hr : IsPGroup 2 r.ker := by
    let k : r.ker →* d.Y :=
      (K.subtype.comp (f.ker.subtype.comp r.ker.subtype)).codRestrict d.Y (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hk : ∀ x : r.ker, k x ∈ pCore 2 d.Y := by
      intro x
      have hfix : (x.val.val : G) ∈ centralizer (d.V : Set G) := by
        have hx : (⟨(x.val.val : G),
          (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
            d.sylow_le) x.val.val.property⟩ : d.M) ∈ d.action.actor.ker := x.val.property
        rw [d.action.ker_actor] at hx
        exact hx
      have hp : (k x : G) ∈ d.Y.pCoreIn 2 := hCY.symm ▸ ⟨(k x).property, hfix⟩
      obtain ⟨y, hy, he⟩ := hp
      exact (show y = k x from Subtype.ext he) ▸ hy
    let k' : r.ker →* pCore 2 d.Y := k.codRestrict _ hk
    apply pCore_isPGroup.of_injective k'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 d.Y => (x.val : G)) hab
  have hp := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup r hr
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- The starred YT quotient is the same quotient as the actual natural
action in the ordinary branch. -/
theorem ordinary_kernel_eq_core (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : (d.Y.subgroupOf d.M).map d.action.actor =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    (restrictedActor d.action (d.Y ⊔ (d.T : Subgroup G))
      (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le)).ker =
        pCore 2 (d.Y ⊔ (d.T : Subgroup G) : Subgroup G) := by
  have he := (restrictedActor d.action (d.Y ⊔ (d.T : Subgroup G))
    (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le)).comap_pCore_of_ker_isPGroup
      (restrictedActor_onto d.M d.Mc d.V d.T d.sylow_le d.action himage)
      (ordinary_kernel_isPGroup d hCY)
  rw [orthogonalActor_twoCore_eq_bot] at he
  exact he

omit [Finite G] in
/-- Every proper hyperplane misses some Y-conjugate of the spanning point.
This chooses the source right-conjugating element of 15.3.54. -/
theorem exists_nonorthogonal_conjugate (d : CharacteristicTwo.LocalData G)
    (Zperp : Subgroup G) (hspan : localSpan d.Z d.Y = d.V)
    (hproper : ¬ d.V ≤ Zperp) :
    ∃ g ∈ d.Y, ¬ Setup.conjugate d.Z g ≤ Zperp := by
  by_contra! hn
  apply hproper
  rw [← hspan]
  apply (closure_le _).mpr
  rintro x ⟨y, hy, z, hz, rfl⟩
  have hh := hn y⁻¹ (d.Y.inv_mem hy)
  exact hh (by
    apply mem_map.mpr
    exact ⟨z, hz, by simp only [inv_inv]; rfl⟩)


/-- The literal star quotient is the full compatible orthogonal actor. -/
noncomputable def ordinaryStarEquiv (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    ((d.Y ⊔ (d.T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (d.Y ⊔ (d.T : Subgroup G) : Subgroup G)) ≃* OrthogonalActor :=
  (QuotientGroup.quotientMulEquivOfEq (ordinary_kernel_eq_core d hCY himage).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (restrictedActor_onto d.M d.Mc d.V d.T d.sylow_le d.action himage))

@[simp] theorem ordinaryStarEquiv_apply_mk (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (x : (d.Y ⊔ (d.T : Subgroup G) : Subgroup G)) :
    ordinaryStarEquiv d hCY himage (QuotientGroup.mk' _ x) =
      restrictedActor d.action (d.Y ⊔ (d.T : Subgroup G))
        (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le) x := by
  rfl

/-- The quotient equivalence preserves each actual ambient action image. -/
theorem ordinaryStarEquiv_map (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp A : Subgroup G) (hA : A ≤ d.Y ⊔ (d.T : Subgroup G)) :
    ((Chapter15.setup d.Z Zperp d.Y d.T).star A).map
      (ordinaryStarEquiv d hCY himage).toMonoidHom = d.action.image A := by
  let K : Subgroup G := d.Y ⊔ (d.T : Subgroup G)
  have hKM : K ≤ d.M := sup_le
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le
  change ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
    (ordinaryStarEquiv d hCY himage).toMonoidHom = _
  ext x
  constructor
  · rintro ⟨q, ⟨k, hk, rfl⟩, rfl⟩
    exact mem_map.mpr ⟨inclusion hKM k, hk, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    let k : K := ⟨m, hA hm⟩
    refine mem_map.mpr ⟨QuotientGroup.mk' _ k,
      mem_map.mpr ⟨k, hm, rfl⟩, ?_⟩
    rfl

/-- Restricting the star equivalence to a marked subgroup retains its
literal image, including the source Y and YU markings. -/
noncomputable def ordinaryStarSubgroupEquiv (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp A : Subgroup G) (hA : A ≤ d.Y ⊔ (d.T : Subgroup G)) :
    (Chapter15.setup d.Z Zperp d.Y d.T).star A ≃* d.action.image A :=
  ((ordinaryStarEquiv d hCY himage).subgroupMap _).trans
    (MulEquiv.subgroupCongr (ordinaryStarEquiv_map d hCY himage Zperp A hA))

@[simp] theorem ordinaryStarSubgroupEquiv_projection
    (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp A : Subgroup G) (hA : A ≤ d.Y ⊔ (d.T : Subgroup G)) (a : A) :
    (ordinaryStarSubgroupEquiv d hCY himage Zperp A hA
      (OrthogonalPlusFour.starProjection (Chapter15.setup d.Z Zperp d.Y d.T) A hA a) :
        OrthogonalActor) = d.action.actor ⟨a,
          (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
            d.sylow_le) (hA a.property)⟩ := by
  change ordinaryStarEquiv d hCY himage
    (QuotientGroup.mk' _ (inclusion hA a)) = _
  rw [ordinaryStarEquiv_apply_mk]
  rfl

/-- The source residual star has the E₉ coordinates demanded by G.2.6. -/
noncomputable def ordinaryResidualModel (d : CharacteristicTwo.LocalData G)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp : Subgroup G) :
    (Chapter15.setup d.Z Zperp d.Y d.T).star d.Y ≃*
      Multiplicative (Fin 2 → ZMod 3) :=
  (ordinaryStarSubgroupEquiv d hCY himage Zperp d.Y le_sup_left).trans
    ((MulEquiv.subgroupCongr himage).trans
      orthogonalActor_residual_equiv_elementaryNine.some)


/-- The exact F.9 setup at the centralizer of the original central involution. -/
noncomputable abbrev f9Setup (d : CharacteristicTwo.LocalData G) : ChapterF.Section09.Setup G :=
  ⟨d.T, d.Y, d.V, d.ZS, d.Z, centralizerH d.Z⟩

/-- The unchanged G.2.1 ambient fields after substituting the actual
perpendicular hyperplane for the fixed-plane seed. -/
theorem g26_base (d : CharacteristicTwo.LocalData G)
    (h : (f9Setup d).Hypothesis)
    (Zperp : Subgroup G) (hZperp : d.ZS ≤ Zperp)
    (hperp : Zperp = d.V ⊓ coreQ d.Z) :
    (Chapter15.setup d.Z Zperp d.Y d.T).BaseHypothesis := by
  let : IsElementaryAbelian 2 d.V := h.elementary
  let D := Chapter15.setup d.Z Zperp d.Y d.T
  let h₀ := h.g2_hypothesis
  have hperpV : Zperp ≤ d.V := hperp.le.trans inf_le_left
  have hTQ : (d.T : Subgroup G) ≤ normalizer (coreQ d.Z : Set G) :=
    h.T_le_H.trans (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := f9Setup d))
  have hTperp : (d.T : Subgroup G) ≤ normalizer (Zperp : Set G) := by
    rw [hperp]
    exact (le_inf h.T_normalizes_V hTQ).trans inf_normalizer_le_normalizer_inf
  refine {
    elementary := IsElementaryAbelian.of_le hperpV
    point_ne_bot := h₀.point_ne_bot
    point_le := h₀.point_le.trans hZperp
    residual := h.residual
    V_le_T := hperpV.trans h.V_le_T
    T_normalizes_point := h.normalizes_point
    T_normalizes_V := hTperp
    T_normalizes_L := h.normalizes_L
    sylow_LT := h₀.sylow_LT
    H_le := h.H_centralizes.trans (centralizer_le_normalizer (d.Z : Set G))
    local_le := h₀.local_le
    sylow_H := h₀.sylow_H
    characteristic_two := h.characteristic_H }

/-- The four G.2.2 conclusions transport through equality of the two
closures; only containment of the new seed in that closure is needed. -/
theorem g26_closure (d : CharacteristicTwo.LocalData G)
    (h : (f9Setup d).Hypothesis)
    (Zperp : Subgroup G) (hZperp : d.ZS ≤ Zperp)
    (hperpU : Zperp ≤ closureU d.Z d.ZS) :
    ClosureConclusions (Chapter15.setup d.Z Zperp d.Y d.T) := by
  let D := Chapter15.setup d.Z Zperp d.Y d.T
  let E := (f9Setup d).g2
  have hU : D.U = E.U := Chapter15.closure_eq hZperp hperpU
  have hc := closureConclusions_of_hypothesis h.g2_hypothesis
  refine {
    central := ?_
    frattini := ?_
    normal := ?_
    reduced := ?_ }
  · constructor
    · change D.tilde Zperp ≤ D.tilde D.U
      rw [hU]
      exact map_mono (comap_mono hperpU)
    · change D.tilde D.U ≤ omegaOneAmbient ((center (D.tilde D.QH)).map (D.tilde D.QH).subtype)
      rw [hU]
      exact hc.central.2
  · rw [hU]
    exact hc.frattini
  · rw [hU]
    exact hc.normal
  · rw [hU]
    exact hc.reduced



open ClassicalOrthogonal.FourPlusMatrix OrthogonalGeometry
attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction

/-- The original central point is exactly the fixed subgroup of the actual
Sylow actor, with the same coordinate embedding. -/
theorem point_eq_map_fixed (d : CharacteristicTwo.LocalData G) :
    d.Z = (fixedVectors (d.action.image d.T)).map d.action.vectorEmbedding := by
  change centralInvolutions d.T = _
  rw [NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane d.T d.sylow_le d.action]
  exact d.action.fixedPlane_eq_map d.sylow_le

/-- Membership in the source central point in the original coordinates. -/
theorem coordinates_mem_fixed_iff (d : CharacteristicTwo.LocalData G) (v : d.V) :
    d.action.coordinates v ∈ fixedVectors (d.action.image d.T) ↔ (v : G) ∈ d.Z := by
  rw [point_eq_map_fixed d]
  have he : d.action.vectorEmbedding (d.action.coordinates v) = (v : G) := by
    simp [NaturalOrthogonalAction.vectorEmbedding]
  rw [← he]
  exact (mem_map_iff_mem d.action.vectorEmbedding_injective).symm

omit [Finite G] in
/-- Transport the actual source53 coordinate equality back through the
original embedding. This is the displacement equality used in source54. -/
theorem map_coordinate_image (d : CharacteristicTwo.LocalData G)
    (A : Subgroup G) (hA : A ≤ d.V) (B : Subgroup OrthogonalVector)
    (hB : (A.subgroupOf d.V).map d.action.coordinates.toMonoidHom = B) :
    B.map d.action.vectorEmbedding = A := by
  have hc : d.action.vectorEmbedding.comp d.action.coordinates.toMonoidHom = d.V.subtype := by
    ext v
    simp [NaturalOrthogonalAction.vectorEmbedding]
  rw [← hB, map_map, hc, map_subgroupOf_eq_of_le hA]

/-- Pull the genuine determinant action back to the original Chapter G
star quotient. Its separate input equations are precisely the finite
coordinate model and the source commutator-hyperplane identification. -/
noncomputable def g26_hypothesis_of_coordinates
    (d : CharacteristicTwo.LocalData G) (h : (f9Setup d).Hypothesis)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp : Subgroup G) (hZS : d.ZS ≤ Zperp)
    (hperp : Zperp = d.V ⊓ coreQ d.Z)
    (hperpU : Zperp ≤ closureU d.Z d.ZS)
    (hspan : localSpan d.Z d.Y = d.V)
    (c : OrthogonalVector ≃* Multiplicative (Mat (F := ZMod 2)))
    (b : d.action.image (d.Y ⊔ closureU d.Z d.ZS) ≃* PairSL (F := ZMod 2))
    (hcomp : ∀ (a : d.action.image (d.Y ⊔ closureU d.Z d.ZS))
      (v : OrthogonalVector),
      (c ((a : OrthogonalActor) • v)).toAdd = matrixAction (b a) (c v).toAdd)
    (hpolar : ∀ v : d.V, (v : G) ∈ Zperp ↔
      ∀ z ∈ fixedVectors (d.action.image d.T),
        determinantForm.polarBilin (c (d.action.coordinates v)).toAdd (c z).toAdd = 0)
    (g : G) (hg : g ∈ d.Y) (hgn : ¬ Setup.conjugate d.Z g ≤ Zperp) :
    Hypothesis (Chapter15.setup d.Z Zperp d.Y d.T) g := by
  let D := Chapter15.setup d.Z Zperp d.Y d.T
  have hc := g26_closure d h Zperp hZS hperpU
  have hU : D.U = closureU d.Z d.ZS := Chapter15.closure_eq hZS hperpU
  have hVL : D.VL = d.V := hspan
  have hYUT : d.Y ⊔ D.U ≤ d.Y ⊔ (d.T : Subgroup G) :=
    sup_le le_sup_left (hc.normal.1.trans le_sup_right)
  have hYUT' : d.Y ⊔ D.U ≤ D.LT := hYUT
  have hYM : d.Y ⊔ D.U ≤ d.M := hYUT.trans
    (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) d.sylow_le)
  let cV : D.VL ≃* Multiplicative (Mat (F := ZMod 2)) :=
    (MulEquiv.subgroupCongr hVL).trans (d.action.coordinates.trans c)
  let bI : d.action.image (d.Y ⊔ D.U) ≃* PairSL (F := ZMod 2) :=
    (MulEquiv.subgroupCongr (congrArg (fun U => d.action.image (d.Y ⊔ U)) hU)).trans b
  let bStar : D.star (d.Y ⊔ D.U) ≃* PairSL (F := ZMod 2) :=
    (ordinaryStarSubgroupEquiv d hCY himage Zperp (d.Y ⊔ D.U) hYUT).trans bI
  refine {
    base := g26_base d h Zperp hZS hperp
    closure := hc
    L_model := ordinaryResidualModel d hCY himage Zperp
    model := bStar
    coordinates := cV
    equivariant := ?_
    point_card := h.point_card
    V_le_VL := (hperp.le.trans inf_le_left).trans_eq hVL.symm
    perpendicular := ?_
    g_mem := hg
    nonorthogonal := hgn }
  · intro a v
    change ↥(d.Y ⊔ D.U) at a
    change ↥D.VL at v
    change (cV.symm (Multiplicative.ofAdd
      (matrixAction (bStar (starProjection D (d.Y ⊔ D.U) hYUT' a))
        (cV v).toAdd)) : G) = (a : G) * v * (a : G)⁻¹
    let av : d.V := d.V.normalizerMonoidHom ⟨a, d.action.normalizes (hYM a.property)⟩
      ((MulEquiv.subgroupCongr hVL) v)
    have hav : (av : G) = (a : G) * v * (a : G)⁻¹ := rfl
    let ai : d.action.image (d.Y ⊔ closureU d.Z d.ZS) :=
      ⟨d.action.actor ⟨a, hYM a.property⟩,
        mem_map.mpr ⟨⟨a, hYM a.property⟩, by
          change (a : G) ∈ d.Y ⊔ closureU d.Z d.ZS
          rw [← hU]
          exact a.property, rfl⟩⟩
    have ha : bStar (starProjection D (d.Y ⊔ D.U) hYUT' a) = b ai := by
      congr 1
    have hev : c (d.action.coordinates av) =
        Multiplicative.ofAdd (matrixAction (b ai) (cV v).toAdd) := by
      apply Multiplicative.toAdd.injective
      have hvcomp := d.action.compatible ⟨a, hYM a.property⟩
        ((MulEquiv.subgroupCongr hVL) v)
      change d.action.coordinates av = (ai : OrthogonalActor) •
        d.action.coordinates ((MulEquiv.subgroupCongr hVL) v) at hvcomp
      rw [hvcomp]
      exact hcomp ai (d.action.coordinates ((MulEquiv.subgroupCongr hVL) v))
    have hev' : cV ((MulEquiv.subgroupCongr hVL).symm av) =
        Multiplicative.ofAdd (matrixAction (b ai) (cV v).toAdd) := by
      simpa only [cV, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using hev
    rw [ha, ← hev', cV.symm_apply_apply]
    exact hav
  · intro v
    change (v : G) ∈ Zperp ↔ ∀ z : d.Z,
      determinantForm.polarBilin (cV v).toAdd
        (cV ⟨z, point_le_VL D z.property⟩).toAdd = 0
    have hpv := hpolar ((MulEquiv.subgroupCongr hVL) v)
    change (v : G) ∈ Zperp ↔ _ at hpv
    refine hpv.trans ?_
    constructor
    · intro hp z
      apply hp
      exact (coordinates_mem_fixed_iff d ⟨z, hVL ▸ point_le_VL D z.property⟩).mpr
        z.property
    · intro hp z hz
      let zv : d.V := d.action.coordinates.symm z
      have hzZ : (zv : G) ∈ d.Z := (coordinates_mem_fixed_iff d zv).mp (by
        simpa only [zv, d.action.coordinates.apply_symm_apply] using hz)
      have hz' := hp ⟨zv, hzZ⟩
      have hzEq : (MulEquiv.subgroupCongr hVL) ⟨(zv : G), point_le_VL D hzZ⟩ = zv := rfl
      change determinantForm.polarBilin
        (c (d.action.coordinates ((MulEquiv.subgroupCongr hVL) v))).toAdd
        (c (d.action.coordinates ((MulEquiv.subgroupCongr hVL)
          ⟨(zv : G), point_le_VL D hzZ⟩))).toAdd = 0 at hz'
      rw [hzEq, d.action.coordinates.apply_symm_apply] at hz'
      exact hz'


/-- The constructed G.2.6 coordinates are the literal determinant coordinates,
retaining the original quadratic marking for later singular-vector consumers. -/
theorem g26_hypothesis_coordinates
    (d : CharacteristicTwo.LocalData G) (h : (f9Setup d).Hypothesis)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp : Subgroup G) (hZS : d.ZS ≤ Zperp)
    (hperp : Zperp = d.V ⊓ coreQ d.Z)
    (hperpU : Zperp ≤ closureU d.Z d.ZS)
    (hspan : localSpan d.Z d.Y = d.V)
    (c : OrthogonalVector ≃* Multiplicative (Mat (F := ZMod 2)))
    (b : d.action.image (d.Y ⊔ closureU d.Z d.ZS) ≃* PairSL (F := ZMod 2))
    (hcomp : ∀ (a : d.action.image (d.Y ⊔ closureU d.Z d.ZS))
      (v : OrthogonalVector),
      (c ((a : OrthogonalActor) • v)).toAdd = matrixAction (b a) (c v).toAdd)
    (hpolar : ∀ v : d.V, (v : G) ∈ Zperp ↔
      ∀ z ∈ fixedVectors (d.action.image d.T),
        determinantForm.polarBilin (c (d.action.coordinates v)).toAdd (c z).toAdd = 0)
    (g : G) (hg : g ∈ d.Y) (hgn : ¬ Setup.conjugate d.Z g ≤ Zperp)
    (v : (Chapter15.setup d.Z Zperp d.Y d.T).VL) :
    (g26_hypothesis_of_coordinates d h hCY himage Zperp hZS hperp hperpU hspan
      c b hcomp hpolar g hg hgn).coordinates v =
        c (d.action.coordinates ((MulEquiv.subgroupCongr hspan) v)) := rfl



open OrthogonalGeometry.Source50Model OrthogonalGeometry.Source50Matrix

private theorem actor_residual_notation :
    Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor) =
      pResidual 2 OrthogonalActor := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact map_pResidual 2 Subgroup.topEquiv

/-- Construct G.2.6 on the original source groups from the earlier ordinary
kernel and hyperplane facts. The compatible determinant model, the source
star quotient, and the nonorthogonal conjugator are all constructed here. -/
theorem exists_g26_hypothesis_marked
    (d : CharacteristicTwo.LocalData G) (h : (f9Setup d).Hypothesis)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp : Subgroup G) (hZS : d.ZS ≤ Zperp)
    (hperp : Zperp = d.V ⊓ coreQ d.Z)
    (hperpU : Zperp ≤ closureU d.Z d.ZS)
    (hspan : localSpan d.Z d.Y = d.V)
    [IsElementaryAbelian 2 (d.action.image (closureU d.Z d.ZS))]
    (hother : ¬ d.action.image (closureU d.Z d.ZS) ≤
      planePart (d.action.sylowImage d.T d.sylow_le))
    (hmovement : (movement (d.action.image (closureU d.Z d.ZS))).map
      d.action.vectorEmbedding = Zperp) :
    ∃ g ∈ d.Y, ∃ h26 : Hypothesis (Chapter15.setup d.Z Zperp d.Y d.T) g,
      ∀ v : (Chapter15.setup d.Z Zperp d.Y d.T).VL,
        determinantForm (h26.coordinates v).toAdd =
          FusionCore.orthogonalCoordinateValue
            (d.action.coordinates ((MulEquiv.subgroupCongr hspan) v)) := by
  let U := closureU d.Z d.ZS
  let R := d.action.image U
  let P := d.action.sylowImage d.T d.sylow_le
  have hUT : U ≤ (d.T : Subgroup G) := h.UH_le_QH.trans h.QH_le_T
  have hUM : U ≤ d.M := hUT.trans d.sylow_le
  have hRP : R ≤ (P : Subgroup OrthogonalActor) := map_mono (comap_mono hUT)
  have hPR : (P : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor) := by
    have ht : (d.T : Subgroup G) ≤ normalizer (U : Set G) :=
      h.T_le_H.trans (H_normalizes_closureU d.Z d.ZS)
    exact (map_mono ((comap_mono ht).trans
      (le_normalizer_comap d.M.subtype))).trans (le_normalizer_map d.action.actor)
  obtain ⟨c, a, hcomp, hq, hpolar⟩ :=
    determinant_model_with_perpendicular P R hRP hPR hother
  have hIimage : d.action.image (d.Y ⊔ U) = R ⊔ pResidual 2 OrthogonalActor := by
    change ((d.Y ⊔ U).subgroupOf d.M).map d.action.actor = _
    rw [subgroupOf_sup (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hUM,
      Subgroup.map_sup]
    change d.action.image d.Y ⊔ R = R ⊔ pResidual 2 OrthogonalActor
    rw [himage, actor_residual_notation, sup_comm]
  let b := (MulEquiv.subgroupCongr hIimage).trans a
  have hcomp' (x : d.action.image (d.Y ⊔ U)) (v : OrthogonalVector) :
      (c ((x : OrthogonalActor) • v)).toAdd = matrixAction (b x) (c v).toAdd :=
    hcomp ((MulEquiv.subgroupCongr hIimage) x) v
  have hpolar' (v : d.V) : (v : G) ∈ Zperp ↔
      ∀ z ∈ fixedVectors (d.action.image d.T),
        determinantForm.polarBilin (c (d.action.coordinates v)).toAdd (c z).toAdd = 0 := by
    rw [← hmovement]
    have he : d.action.vectorEmbedding (d.action.coordinates v) = (v : G) := by
      simp [NaturalOrthogonalAction.vectorEmbedding]
    rw [← he, mem_map_iff_mem d.action.vectorEmbedding_injective]
    exact hpolar (d.action.coordinates v)
  have hperpcard : Nat.card Zperp = 8 := by
    rw [← hmovement, card_map_of_injective d.action.vectorEmbedding_injective]
    exact movement_card_eight P R hRP hPR hother
  have hproper : ¬ d.V ≤ Zperp := by
    intro hv
    have hc := card_le_of_le hv
    rw [d.action.card_vector, hperpcard] at hc
    omega
  obtain ⟨g, hg, hgn⟩ := exists_nonorthogonal_conjugate d Zperp hspan hproper
  refine ⟨g, hg, g26_hypothesis_of_coordinates d h hCY himage Zperp hZS hperp hperpU
    hspan c b hcomp' hpolar' g hg hgn, ?_⟩
  intro v
  rw [g26_hypothesis_coordinates]
  exact hq _

/-- Unmarked projection of the quadratic-compatible source54 construction. -/
theorem exists_g26_hypothesis
    (d : CharacteristicTwo.LocalData G) (h : (f9Setup d).Hypothesis)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp : Subgroup G) (hZS : d.ZS ≤ Zperp)
    (hperp : Zperp = d.V ⊓ coreQ d.Z)
    (hperpU : Zperp ≤ closureU d.Z d.ZS)
    (hspan : localSpan d.Z d.Y = d.V)
    [IsElementaryAbelian 2 (d.action.image (closureU d.Z d.ZS))]
    (hother : ¬ d.action.image (closureU d.Z d.ZS) ≤
      planePart (d.action.sylowImage d.T d.sylow_le))
    (hmovement : (movement (d.action.image (closureU d.Z d.ZS))).map
      d.action.vectorEmbedding = Zperp) :
    ∃ g ∈ d.Y, Nonempty (Hypothesis (Chapter15.setup d.Z Zperp d.Y d.T) g) := by
  obtain ⟨g, hg, h26, _⟩ := exists_g26_hypothesis_marked d h hCY himage Zperp hZS
    hperp hperpU hspan hother hmovement
  exact ⟨g,hg,⟨h26⟩⟩

open scoped Pointwise IsMulCommutative
open Representation.BinaryQuadraticPair

open Chapter15Assembly Chapter15Collapse Multiplicity.Chapter15Exchange

/-- The original source54 consumer, with the conjugator and its genuine G.2.6
hypothesis constructed from the ordinary source48–53 facts. All five printed
clauses use the original ambient subgroups and the literal module quotient. -/
theorem literal_source54
    (d : CharacteristicTwo.LocalData G) (h : (f9Setup d).Hypothesis)
    (hCY : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (Zperp : Subgroup G) (hZS : d.ZS ≤ Zperp)
    (hperp : Zperp = d.V ⊓ coreQ d.Z)
    (hperpU : Zperp ≤ closureU d.Z d.ZS)
    (hspan : localSpan d.Z d.Y = d.V)
    [IsElementaryAbelian 2 (d.action.image (closureU d.Z d.ZS))]
    (hother : ¬ d.action.image (closureU d.Z d.ZS) ≤
      planePart (d.action.sylowImage d.T d.sylow_le))
    (hmovement : (movement (d.action.image (closureU d.Z d.ZS))).map
      d.action.vectorEmbedding = Zperp) :
    ∃ g ∈ d.Y, ∃ h26 : Hypothesis (Chapter15.setup d.Z Zperp d.Y d.T) g,
    letI := moduleSectionNormal h26 h26.I_eq_LU
    letI := moduleSectionElementary h26 h26.I_eq_LU h26.S_normalizes_U h26.S_eq_coreProduct
    ∃ f : FactorData (pairI d.Z d.ZS g) (pairP d.Z d.ZS g) d.V d.Y
        (Additive (Quotient (Chapter15.setup d.Z Zperp d.Y d.T) g)),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ∧
      pairI d.Z d.ZS g = d.Y ⊔ closureU d.Z d.ZS ∧
      pairP d.Z d.ZS g = pairW d.Z d.ZS g ⊔ rightConjugate (pairW d.Z d.ZS g) g ∧
      (pairI d.Z d.ZS g : Set G) = (d.Y : Set G) * (closureU d.Z d.ZS : Set G) ∧
      (pairP d.Z d.ZS g : Set G) = (pairW d.Z d.ZS g : Set G) *
        (rightConjugate (pairW d.Z d.ZS g) g : Set G) ∧
      d.V ≤ pairP d.Z d.ZS g ⊓ centralizer (pairP d.Z d.ZS g : Set G) ∧
      closureU d.Z d.ZS ⊓ rightConjugate (closureU d.Z d.ZS) g =
        Zperp ⊓ rightConjugate Zperp g ∧
      pairW d.Z d.ZS g ⊓ rightConjugate (pairW d.Z d.ZS g) g =
        closureU d.Z d.ZS ⊓ rightConjugate (closureU d.Z d.ZS) g ∧
      Nonempty ((closureU d.Z d.ZS ⊓ rightConjugate (closureU d.Z d.ZS) g : Subgroup G) ≃*
        Multiplicative (Fin 2 → ZMod 2)) ∧
      Nonempty ((pairW d.Z d.ZS g ⊓ rightConjugate (pairW d.Z d.ZS g) g : Subgroup G) ≃*
        Multiplicative (Fin 2 → ZMod 2)) ∧
      Nonempty (FactorModuleConclusion (pairI d.Z d.ZS g) (pairP d.Z d.ZS g) d.V d.Y
        (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI d.Z d.ZS g))))
          f.representation) ∧
      rightConjugate (pairW d.Z d.ZS g) g ≤ normalizer (closureU d.Z d.ZS : Set G) ∧
      ⁅rightConjugate (pairW d.Z d.ZS g) g, closureU d.Z d.ZS⁆ ≤ pairW d.Z d.ZS g := by
  obtain ⟨g, hg, ⟨h26⟩⟩ := exists_g26_hypothesis d h hCY himage Zperp hZS hperp
    hperpU hspan hother hmovement
  refine ⟨g, hg, h26, ?_⟩
  have hSyl : ∃ P : Sylow 2 d.M, (P : Subgroup d.M).map d.M.subtype = d.T := by
    exact ⟨d.T.subtype d.sylow_le, map_subgroupOf_eq_of_le d.sylow_le⟩
  exact literal_application d.action d.sylow_le hSyl hZS hperpU hspan h26 rfl

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
