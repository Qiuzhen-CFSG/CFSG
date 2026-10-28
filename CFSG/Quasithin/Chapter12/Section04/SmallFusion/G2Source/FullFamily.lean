module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedCentralizerCover
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2Detector
public import Theory.GroupTheory.PResidual.SylowCentralizer
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction
public import Mathlib.GroupTheory.Abelianization.Defs
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.G2BinaryPointCentralizer
public import Theory.Representation.G2BinaryPointOffenders
public import Theory.Representation.G2OrthogonalCover.BinaryOffenders
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.PointGeometry
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.MovedOffenderImage

/-!
# The common image of the full maximum elementary family

The original residual-Sylow join is the omega-center centralizer inside LT.
Its core maps into the radical of the natural point stabilizer. Every maximum
elementary subgroup outside the actor kernel is an offender, so the binary
point-offender theorem identifies all their images with that of the moved core.
The final theorem retains the original quotient actor and right conjugation.

Source: Aschbacher--Smith 3.3.28, printed p.601; B.2.21 and B.4.6.
-/

public section
open Subgroup
open scoped Pointwise
open scoped IsMulCommutative

namespace G2FullFamilyBridge

variable {G K : Type*} [Group G] [Group K]

/-- The residual-Sylow product is the literal centralizer inside LT. -/
theorem residual_sup_eq_centralizer_intersection [Finite G]
    (T : Sylow 2 G) (L : Subgroup G) (E : Set G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTC : (T : Subgroup G) ≤ centralizer E) :
    (pResidual 2 (L ⊓ centralizer E : Subgroup G)).map
        (L ⊓ centralizer E).subtype ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ centralizer E := by
  have hnorm : (T : Subgroup G) ≤ normalizer (L ⊓ centralizer E : Set G) :=
    (le_inf hTL (hTC.trans (centralizer E).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [embedded_pResidual_sup_sylow_of_normalizes T _ hnorm]
  apply le_antisymm
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hTC)
  · rintro g ⟨hg,hgC⟩
    have hm : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L _ hTL]
      exact hg
    obtain ⟨l,hl,t,ht,rfl⟩ := hm
    have hlC := (centralizer E).mul_mem hgC ((centralizer E).inv_mem (hTC ht))
    rw [mul_inv_cancel_right] at hlC
    exact mul_mem_sup ⟨hl,hlC⟩ ht

/-- A relative normal image places the original core in the larger core.
No hypothesis on the kernel is needed for this containment. -/
theorem map_core_le_core_of_normal_image
    (p : ℕ) (f : G →* K) (J P : Subgroup G) (B : Subgroup K)
    (himage : J.map f = B ⊓ P.map f)
    (hderived : commutator K ≤ P.map f) :
    (J.pCoreIn p).map f ≤ B.pCoreIn p := by
  let : (P.map f).Normal := Subgroup.Normal.of_commutator_le K hderived
  have hBnorm : B ≤ normalizer (J.map f : Set K) := by
    rw [himage]
    exact (le_inf B.le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hJnorm : J ≤ normalizer (J.pCoreIn p : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore p J))
  have hnorm : J.map f ≤ normalizer ((J.pCoreIn p).map f : Set K) :=
    (map_mono hJnorm).trans (le_normalizer_map f)
  have hcore : (J.pCoreIn p).map f ≤ (J.map f).pCoreIn p :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn p J).map f)
      (map_mono (pCoreIn_le p J)) hnorm
  exact hcore.trans (pCoreIn_mono_of_normalizes (himage ▸ inf_le_left) hBnorm)

/-- The same bound uses the literal restricted ambient core in the source. -/
theorem restricted_core_image_le
    (p : ℕ) (N H J : Subgroup G) (hJN : J ≤ N) (f : N →* K) (B : Subgroup K)
    (himage : (J.subgroupOf N).map f = B ⊓ (H.subgroupOf N).map f)
    (hderived : commutator K ≤ (H.subgroupOf N).map f) :
    ((J.pCoreIn p).subgroupOf N).map f ≤ B.pCoreIn p := by
  rw [← pCoreIn_subgroupOf p J N hJN]
  exact map_core_le_core_of_normal_image p f _ _ B himage hderived

open Representation Representation.BinaryOffender

/-- The full maximum elementary family transports to a prescribed actor.
This does not require the maximum elementary subgroup to be normal. -/
theorem maxElementary_model_offender
    [Finite G] (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) K M)
    (φ : G →* K) (hker : φ.ker = centralizer (U : Set G))
    (b : U ≃* Multiplicative M)
    (he : ∀ (g : G) (v : U),
      (b (MulAut.conjNormal g v)).toAdd = σ (φ g) (b v).toAdd)
    (S A : Subgroup G) (hUS : U ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hne : ¬ A ≤ φ.ker) : IsOffender σ (A.map φ) := by
  let : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let q := φ.rangeRestrict
  have hk : q.ker = centralizer (U : Set G) := φ.ker_rangeRestrict.trans hker
  let ρ := NormalElementaryQuotient.representation U q φ.rangeRestrict_surjective hk
  let E : Additive U ≃ₗ[ZMod 2] M :=
    LinearEquiv.ofBijective (b.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) b.bijective
  have hE (g : φ.range) (v : Additive U) : E (ρ g v) = σ g.val (E v) := by
    obtain ⟨g,rfl⟩ := φ.rangeRestrict_surjective g
    have hh : (ρ (q g) v).toMul = MulAut.conjNormal g v.toMul :=
      Subtype.ext (NormalElementaryQuotient.representation_apply U q
        φ.rangeRestrict_surjective hk g v)
    change (b (ρ (q g) v).toMul).toAdd = σ (φ g) (b v.toMul).toAdd
    rw [hh]
    exact he g v.toMul
  have ho := NormalElementaryQuotient.maxElementary_isOffender U q
    φ.rangeRestrict_surjective hk S A hUS hA (by rwa [φ.ker_rangeRestrict])
  have ht := ho.map_equivariant ρ σ φ.range.subtype φ.range.subtype_injective E hE
  have hc : φ.range.subtype.comp q = φ := by ext g; rfl
  simpa only [map_map, hc] using ht


open Atlas.G2
local notation "F" => ZMod 2

theorem exists_point_conjugator
    (f : G →* Model F) (C : Subgroup G) (v : Natural.Space F) (hv : v ≠ 0)
    (hC : ∀ a, a ∈ C ↔ Natural.action F (f a) v = v) :
    ∃ g : Model F, ∀ a, a ∈ C ↔
      Restricted.NaturalCoordinates.action F
        ((MulAut.conj g).toMonoidHom.comp f a) (Pi.single 0 1) = Pi.single 0 1 := by
  let E := Restricted.NaturalCoordinates.equiv F
  let z : Natural.Space F := E.symm (Pi.single 0 1)
  have hz : z ≠ 0 := by
    intro h
    have hh : (Pi.single 0 1 : Fin 6 → F) = 0 := by
      simpa only [z, E.apply_symm_apply, map_zero] using congrArg E h
    have hh0 := congrFun hh 0
    simp at hh0
  obtain ⟨g,hg⟩ := Natural.derivedAction_transitive F v z hv hz
  let f' := (MulAut.conj (g : Model F)).toMonoidHom.comp f
  have hpoint : E (Natural.action F (g : Model F) v) = Pi.single 0 1 := by
    change E (Natural.derivedAction F g v) = _
    rw [hg]
    exact E.apply_symm_apply _
  have hconj (a : G) : Natural.action F (f' a)
      (Natural.action F (g : Model F) v) =
      Natural.action F (g : Model F) (Natural.action F (f a) v) := by
    change Natural.action F ((g : Model F) * f a * (g : Model F)⁻¹)
      (Natural.action F (g : Model F) v) = _
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  refine ⟨g, ?_⟩
  intro a
  change a ∈ C ↔ Restricted.NaturalCoordinates.action F (f' a)
    (Pi.single 0 1) = Pi.single 0 1
  rw [← hpoint]
  have hc := LinearMap.congr_fun
    ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (f' a))
    (Natural.action F (g : Model F) v)
  change E (Natural.action F (f' a) (Natural.action F (g : Model F) v)) =
    Restricted.NaturalCoordinates.action F (f' a)
      (E (Natural.action F (g : Model F) v)) at hc
  rw [← hc, E.injective.eq_iff, hconj,
    ((Natural.action F).apply_bijective (g : Model F)).1.eq_iff]
  exact hC a

theorem marked_point_core_image_le_radical
    (f : G →* Model F) (H C : Subgroup G)
    (hderived : commutator (Model F) ≤ H.map f)
    (hC : ∀ a, a ∈ C ↔ Restricted.NaturalCoordinates.action F (f a)
      (Pi.single 0 1) = Pi.single 0 1) :
    ((C ⊓ H).pCoreIn 2).map f ≤ LieParabolicSetup.radical₂ := by
  have hm := Natural.BinaryPointFlag.marked_point_image
    (f.comp H.subtype) (C.subgroupOf H) (fun a => hC a)
  rw [← map_map, subgroupOf_map_subtype, MonoidHom.range_comp, range_subtype] at hm
  have hc := map_core_le_core_of_normal_image 2 f (C ⊓ H) H
    BinaryCore.secondParabolic hm hderived
  rwa [← LieParabolicSetup.local₂_binary, LieParabolicSetup.local₂_pCoreIn] at hc

/-- Every offender in the original point-centralizer core has the same image. -/
theorem point_core_offender_images_eq
    (f : G →* Model F) (H C A B : Subgroup G)
    (hderived : commutator (Model F) ≤ H.map f)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hC : ∀ a, a ∈ C ↔ Natural.action F (f a) v = v)
    (hA : A ≤ (C ⊓ H).pCoreIn 2) (hB : B ≤ (C ⊓ H).pCoreIn 2)
    (hoA : IsOffender (Natural.traceZeroAction F) (A.map f))
    (hoB : IsOffender (Natural.traceZeroAction F) (B.map f)) :
    A.map f = B.map f := by
  obtain ⟨g,hg⟩ := exists_point_conjugator f C v hv hC
  let α := (MulAut.conj g).toMonoidHom
  let f' := α.comp f
  have hderived' : commutator (Model F) ≤ H.map f' := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ commutator (Model F) := by
      simpa only [inv_inv] using
        (inferInstance : (commutator (Model F)).Normal).conj_mem x hx g⁻¹
    obtain ⟨a,ha,he⟩ := hderived hx'
    refine ⟨a,ha,?_⟩
    change g * f a * g⁻¹ = x
    rw [he]
    group
  have hcore := marked_point_core_image_le_radical f' H C hderived' hg
  have step (Y : Subgroup G) (hY : Y ≤ (C ⊓ H).pCoreIn 2)
      (hoY : IsOffender (Natural.traceZeroAction F) (Y.map f)) :
      Y.map f' = BinaryCore.elementary := by
    have hon : IsOffender (Natural.action F) (Y.map f) :=
      (Natural.OrthogonalCover.BinaryOffenders.offender_iff_natural _).mp hoY
    have hoc : IsOffender (Natural.action F) ((Y.map f).map α) := by
      refine ⟨hon.1.map_conj g, ?_⟩
      rw [fixedCodim_map_conj, rank_map_conj]
      exact hon.2
    have hoe : IsOffender (Restricted.NaturalCoordinates.action F) (Y.map f') := by
      have he (x : Model F) (w : Natural.Space F) :
          Restricted.NaturalCoordinates.equiv F (Natural.action F x w) =
          Restricted.NaturalCoordinates.action F x (Restricted.NaturalCoordinates.equiv F w) :=
        LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' x) w
      have hh := hoc.map_equivariant (Natural.action F) (Restricted.NaturalCoordinates.action F)
        (MonoidHom.id _) Function.injective_id (Restricted.NaturalCoordinates.equiv F) he
      simpa only [map_id, map_map, MonoidHom.id_comp, f'] using hh
    exact Natural.BinaryPointOffenders.offender_eq_elementary _ hoe ((map_mono hY).trans hcore)
  apply map_injective (f := α) (MulAut.conj g).injective
  rw [map_map, map_map]
  exact (step A hA hoA).trans (step B hB hoB).symm


namespace Source
open CFSG.Quasithin
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Chapter12.Section04.SmallFusion.G2Source
open ChapterB.QuasisimpleSource Theory.GroupTheory

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem exists_full_family_common_image
    (h : Hypothesis1223 CFSG.KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At CFSG.KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (Natural.OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d⁻¹).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ q : omegaResidualCore T L →* Model F,
      q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (omegaResidualCore T L) ∧
      ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (omegaResidualCore T L)),
        ¬ A ≤ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (omegaResidualCore T L) →
        A.map q = ((((L ⊔ (T : Subgroup G)).pCoreIn 2).map
          (MulAut.conj d⁻¹).toMonoidHom).subgroupOf (omegaResidualCore T L)).map q := by
  classical
  let N := normalizer (L : Set G)
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let R := omegaResidualCore T L
  let Z := omegaCenterIn (T : Subgroup G)
  let C := (centralizer (Z : Set G)).subgroupOf N
  let J := omegaLocalResidual T L ⊔ (T : Subgroup G)
  let B := V.map (MulAut.conj d⁻¹).toMonoidHom
  let W := Q.map (MulAut.conj d⁻¹).toMonoidHom
  have hd' := (normalizer (T : Set G)).inv_mem hd
  have hRN : R ≤ N := local_core_containments.2.trans D.sylow_normalizes_component
  have hVR : V ≤ R := D.le_core.trans local_core_containments.1
  have hBR : B ≤ R := conjugate_chosen_le_local_core h D structural e hne hd'
  have hW : R ⊓ centralizer (B : Set G) = W :=
    local_centralizer_conjugate_eq_core_conjugate h D structural e hne hd'
  have hWR : W ≤ R := hW.symm.le.trans inf_le_left
  have hWC : W ≤ centralizer (B : Set G) := hW.symm.le.trans inf_le_right
  have hBW : B ≤ W := map_mono D.le_core
  have hTC : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mp
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  have hJ : J = H ⊓ centralizer (Z : Set G) :=
    residual_sup_eq_centralizer_intersection T L _ D.sylow_normalizes_component hTC
  have hJN : J ≤ N := hJ.le.trans (inf_le_left.trans
    (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hcore : (C ⊓ H.subgroupOf N).pCoreIn 2 = R.subgroupOf N := by
    have hj : C ⊓ H.subgroupOf N = J.subgroupOf N := by
      ext x
      change ((x : G) ∈ centralizer (Z : Set G) ∧ (x : G) ∈ H) ↔ (x : G) ∈ J
      rw [hJ]
      exact and_comm
    rw [hj, pCoreIn_subgroupOf 2 J N hJN]
    rfl
  obtain ⟨b,ψ,hψ,hψL⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  have hderived : commutator (Model F) ≤ (H.subgroupOf N).map ψ := by
    intro g hg
    obtain ⟨l,hl⟩ :=
      (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) ⟨g,hg⟩
    refine ⟨⟨l, L.le_normalizer l.property⟩,
      (le_sup_left : L ≤ H) l.property, ?_⟩
    rw [hψL]
    exact congrArg Subtype.val hl
  have hrange : commutator (Model F) ≤ ψ.range := hderived.trans (map_le_range _ _)
  obtain ⟨v,hv,hpoint⟩ := exists_omega_point_for_full_g2_actor h D structural e hne
    hescape b ψ hψ
  let i := inclusion hRN
  let q := ψ.comp i
  have hq (r : R) (x : Natural.TraceZero F) := hψ (i r) x
  have hk : q.ker = Q.subgroupOf R := by
    rw [full_g2_actor_ker_eq_centralizer R b q hq]
    dsimp only [Q, H]
    rw [← local_centralizer_chosen_eq_core h D structural, inf_subgroupOf_left]
  let U := V.subgroupOf R
  let : IsElementaryAbelian 2 V := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVR
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (local_core_containments.2.trans (((structural L h).2.2 V D).1))
  let bR : U ≃* Multiplicative (Natural.TraceZero F) := (subgroupOfEquivOfLe hVR).trans b
  have hkU : q.ker = centralizer (U : Set R) := by
    rw [full_g2_actor_ker_eq_centralizer R b q hq]
    ext r
    constructor
    · intro hr u hu
      exact Subtype.ext (hr u.val hu)
    · intro hr u hu
      exact congrArg Subtype.val (hr ⟨u,hVR hu⟩ hu)
  have he (r : R) (u : U) :
      (bR (MulAut.conjNormal r u)).toAdd =
        Natural.traceZeroAction F (q r) (bR u).toAdd := by
    apply Multiplicative.ofAdd.injective
    change b ((subgroupOfEquivOfLe hVR) (MulAut.conjNormal r u)) =
      Multiplicative.ofAdd (Natural.traceZeroAction F (q r)
        (b ((subgroupOfEquivOfLe hVR) u)).toAdd)
    apply b.symm.injective
    change b.symm (b ((subgroupOfEquivOfLe hVR) (MulAut.conjNormal r u))) =
      b.symm (Multiplicative.ofAdd
        (Natural.traceZeroAction F (ψ (i r))
          (b ((subgroupOfEquivOfLe hVR) u)).toAdd))
    apply Subtype.ext
    rw [b.symm_apply_apply, hψ, ofAdd_toAdd, b.symm_apply_apply]
    rfl
  have himage (Y : Subgroup G) (hYR : Y ≤ R) :
      (Y.subgroupOf R).map q = (Y.subgroupOf N).map ψ := by
    change (Y.subgroupOf R).map (ψ.comp i) = _
    rw [← map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val,hYR hx⟩,hx,rfl⟩
  have hoffB := (moved_full_actor_offender_image h D structural e hne b ψ hψ hd' hmove).1
  have hcB := (moved_full_actor_offender_image h D structural e hne b ψ hψ hd' hmove).2
  have hself := full_actor_moved_image_selfcentralizing h D structural e hne hescape
    hd' b ψ hψ hrange hcB
  have hWB : (W.subgroupOf N).map ψ = (B.subgroupOf N).map ψ := by
    apply le_antisymm
    · apply le_trans (le_inf (map_le_range _ _) ?_) hself
      have hc : W.subgroupOf N ≤ centralizer (B.subgroupOf N : Set N) := by
        intro w hw z hz
        exact Subtype.ext (hWC hw z.val hz)
      exact (map_mono hc).trans (map_centralizer_le_centralizer_image _ ψ)
    · exact map_mono (subgroupOf_mono N hBW)
  refine ⟨q,hk,?_⟩
  intro A hA hAn
  have ho := maxElementary_model_offender U (Natural.traceZeroAction F) q hkU bR he
    ⊤ A le_top hA (by rwa [hk])
  let AN := A.map i
  have hAN : AN ≤ (C ⊓ H.subgroupOf N).pCoreIn 2 := by
    rw [hcore]
    rintro _ ⟨a,ha,rfl⟩
    exact a.property
  have hBN : B.subgroupOf N ≤ (C ⊓ H.subgroupOf N).pCoreIn 2 := by
    rw [hcore]
    exact subgroupOf_mono N hBR
  have hoAN : IsOffender (Natural.traceZeroAction F) (AN.map ψ) := by
    simpa only [AN,map_map] using ho
  have hcommon := point_core_offender_images_eq ψ (H.subgroupOf N) C AN (B.subgroupOf N)
    hderived v hv hpoint hAN hBN hoAN hoffB
  calc
    A.map q = AN.map ψ := by
      change A.map (ψ.comp i) = (A.map i).map ψ
      rw [map_map]
    _ = (B.subgroupOf N).map ψ := hcommon
    _ = (W.subgroupOf N).map ψ := hWB.symm
    _ = (W.subgroupOf R).map q := (himage W hWR).symm

end Source

end G2FullFamilyBridge
