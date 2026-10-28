module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Parabolic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceResiduals
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MarkedExtension
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# The marked plus action and its local residual

The plus action is the literal conjugation action on W_K. Its stabilizer
of the original seed z is therefore the image of the actual centralizer,
including the action kernel. Transporting this equality carries the source
O^{3′}(C_K(z)) through exactly the same map. With a two-group action kernel,
the two-core and the quotient by it are transported as well.

The symmetric extension is induced by conjugation on the marked K⁺. It
retains its chosen A₈ identification on every element of K⁺. These are
conditional transport results: recognition of the orthogonal module,
identification of the marked seed stabilizer, and the concrete four-block
residual and wreath calculation remain required for source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
paragraph following 13.6.23, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
open ComponentSelection
open Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G]

/-- The actual actor is KTᵥ once 13.6.14 and 13.6.20 are available. -/
theorem plusActor_eq (K L T : Subgroup G) (v : G)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    plusActor K L T v = K ⊔ Tv T v := by
  rw [plusActor, Kminus_eq_of_invariant K T v hK, sup_eq_left.mpr hLK]

variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The original seed, before taking the quotient of U_K by its fixed submodule. -/
def markedSeed : WK K L T z v :=
  ⟨z, le_conjugateSpanBy (zpowers z) _ (mem_zpowers z)⟩

/-- The literal stabilizer of z in the faithful plus action on W_K. -/
def seedStabilizer : Subgroup (Gplus K L T z v hL hz) :=
  (MulAction.stabilizer (MulAut (WK K L T z v)) (markedSeed K L T z v)).comap
    (plusAction K L T z v hL hz)

/-- Fixing the marked seed is exactly centralizing z upstairs. -/
theorem mk_mem_seedStabilizer (a : plusActor K L T v) :
    plusMk K L T z v hL hz a ∈ seedStabilizer K L T z v hL hz ↔
      (a : G) ∈ Gv z := by
  change plusAction K L T z v hL hz (plusMk K L T z v hL hz a)
      (markedSeed K L T z v) = markedSeed K L T z v ↔ _
  rw [Subtype.ext_iff]
  change (a : G) * z * (a : G)⁻¹ = z ↔ (a : G) ∈ centralizer ({z} : Set G)
  rw [mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff]

/-- The actual centralizer image is the intersection with the marked stabilizer.
No lifting from an arbitrary fixed-space quotient is used. -/
theorem plusImage_centralizer :
    plusImage K L T z v hL hz (K ⊓ Gv z) =
      plusImage K L T z v hL hz K ⊓ seedStabilizer K L T z v hL hz := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, (mk_mem_seedStabilizer K L T z v hL hz x).mpr hx.2⟩
  · rintro ⟨⟨x, hx, rfl⟩, hf⟩
    exact ⟨x, ⟨hx, (mk_mem_seedStabilizer K L T z v hL hz x).mp hf⟩, rfl⟩

/-- Plus images preserve joins of subgroups lying in the actual actor. -/
theorem plusImage_sup (H D : Subgroup G)
    (hH : H ≤ plusActor K L T v) (hD : D ≤ plusActor K L T v) :
    plusImage K L T z v hL hz (H ⊔ D) =
      plusImage K L T z v hL hz H ⊔ plusImage K L T z v hL hz D := by
  rw [plusImage, subgroupOf_sup hH hD, Subgroup.map_sup]
  rfl

/-- K⁺ and the actual image of Tᵥ generate the whole plus actor. -/
theorem plusComponent_sup_Tv
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    plusImage K L T z v hL hz K ⊔ plusImage K L T z v hL hz (Tv T v) = ⊤ := by
  rw [← plusImage_sup K L T z v hL hz K (Tv T v)
    (K_le_plusActor K L T v) le_sup_right, ← plusActor_eq K L T v hK hLK,
    plusImage, subgroupOf_self, map_top_of_surjective _ (plusMk_surjective K L T z v hL hz)]

/-- The marked A₈ and an outside actor give a compatible S₈ equivalence.
The self-centralizer premise is retained until the source FF reduction supplies it. -/
noncomputable def symmetricEquiv
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8) := by
  let : (plusImage K L T z v hL hz K).Normal :=
    plusComponent_normal K L T z v hL hz hLK hK
  exact BinaryLinear.InvariantNodeActions.symmetricExtension _ e hc
    (fun h => hout (h ▸ le_top))

/-- Compatibility on the literal plus image of the component. -/
theorem symmetricEquiv_on_component
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (k : plusImage K L T z v hL hz K) :
    symmetricEquiv K L T z v hL hz hK hLK e hc hout k = (e k).val := by
  let : (plusImage K L T z v hL hz K).Normal :=
    plusComponent_normal K L T z v hL hz hLK hK
  exact BinaryLinear.InvariantNodeActions.symmetricExtension_on_subgroup _ e hc (fun h => hout (h ▸ le_top)) k

/-- The chosen symmetric equivalence sends the component image to the actual A₈. -/
theorem symmetricEquiv_component_image
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    (plusImage K L T z v hL hz K).map
      (symmetricEquiv K L T z v hL hz hK hLK e hc hout).toMonoidHom =
        alternatingGroup (Fin 8) := by
  let : (plusImage K L T z v hL hz K).Normal :=
    plusComponent_normal K L T z v hL hz hLK hK
  exact BinaryLinear.InvariantNodeActions.symmetricExtension_map _ e hc (fun h => hout (h ▸ le_top))

/-- Restrict the literal plus quotient to H and its actual image. -/
noncomputable def imageProjection (H : Subgroup G) (hH : H ≤ plusActor K L T v) :
    H →* plusImage K L T z v hL hz H :=
  ((plusMk K L T z v hL hz).subgroupMap (H.subgroupOf (plusActor K L T v))).comp
    (subgroupOfEquivOfLe hH).symm.toMonoidHom

theorem imageProjection_surjective (H : Subgroup G) (hH : H ≤ plusActor K L T v) :
    Function.Surjective (imageProjection K L T z v hL hz H hH) :=
  ((plusMk K L T z v hL hz).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hH).symm.surjective

/-- Compatibility is with representatives in the original ambient subgroup H. -/
theorem imageProjection_apply (H : Subgroup G) (hH : H ≤ plusActor K L T v) (x : H) :
    (imageProjection K L T z v hL hz H hH x : Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion hH x) := rfl

/-- The restricted action has a two-group kernel when the original plus action does. -/
theorem imageProjection_kernel (H : Subgroup G) (hH : H ≤ plusActor K L T v)
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker) :
    IsPGroup 2 (imageProjection K L T z v hL hz H hH).ker := by
  let f : (imageProjection K L T z v hL hz H hH).ker →*
      (plusMk K L T z v hL hz).ker :=
    ((inclusion hH).comp (imageProjection K L T z v hL hz H hH).ker.subtype).codRestrict
      (plusMk K L T z v hL hz).ker (by
        intro x
        exact congrArg Subtype.val x.property)
  exact hk.of_injective f (by
    intro x y hxy
    have ha : inclusion hH x.val = inclusion hH y.val := congrArg Subtype.val hxy
    exact Subtype.ext (inclusion_injective hH ha))



/-- Trivial two-core and a two-subgroup supplement discharge the centralizer
premise for the actual component image. -/
theorem plusComponent_centralizer_eq_bot
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥ := by
  let C := plusImage K L T z v hL hz K
  let S := plusImage K L T z v hL hz (Tv T v)
  let : C.Normal := plusComponent_normal K L T z v hL hz hLK hK
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  have hnoncomm : ¬ IsMulCommutative C := by
    intro h
    have hA : IsMulCommutative (alternatingGroup (Fin 8)) :=
      isMulCommutative_iff.mpr (fun a b => e.symm.injective (by
        simpa only [map_mul] using (isMulCommutative_iff.mp h) (e.symm a) (e.symm b)))
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp hA
    norm_num at this
  have hS : IsPGroup 2 S := hT.comap_subtype.map (plusMk K L T z v hL hz)
  let q := QuotientGroup.mk' C
  have hqC : C.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hqS : S.map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) (plusComponent_sup_Tv K L T z v hL hz hK hLK)
    change (C ⊔ S).map q = (⊤ : Subgroup _).map q at hh
    rw [Subgroup.map_sup, hqC, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective C)] at hh
    exact hh
  have hquot : IsPGroup 2 ((Gplus K L T z v hL hz) ⧸ C) := by
    have hp := hS.map q
    rw [hqS] at hp
    exact hp.of_equiv Subgroup.topEquiv
  exact Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient C hnoncomm hquot hcore

/-- A source two-subgroup supplement and the R₂ two-core conclusion suffice
for the compatible symmetric extension of the literal plus actor. -/
theorem exists_marked_symmetricEquiv
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    ∃ E : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8),
      (∀ k : plusImage K L T z v hL hz K, E k = (e k).val) ∧
        (plusImage K L T z v hL hz K).map E.toMonoidHom = alternatingGroup (Fin 8) := by
  have hc := plusComponent_centralizer_eq_bot K L T z v hL hz hK hLK e hT hcore
  exact ⟨symmetricEquiv K L T z v hL hz hK hLK e hc hout,
    symmetricEquiv_on_component K L T z v hL hz hK hLK e hc hout,
    symmetricEquiv_component_image K L T z v hL hz hK hLK e hc hout⟩

section Finite
variable [Finite G]

/-- Restriction and ambient embedding commute with taking O^{3′}.
In particular this is the plus image of the source X, not O³ or O₃′. -/
theorem plusImage_orthogonalResidual :
    plusImage K L T z v hL hz (Source.orthogonalResidual K z) =
      (primeToResidual 3 (plusImage K L T z v hL hz (K ⊓ Gv z))).map
        (plusImage K L T z v hL hz (K ⊓ Gv z)).subtype := by
  let A := plusActor K L T v
  let C := (K ⊓ Gv z).subgroupOf A
  have hCA : K ⊓ Gv z ≤ A := inf_le_left.trans (K_le_plusActor K L T v)
  have he : ((primeToResidual 3 C).map C.subtype).map A.subtype =
      Source.orthogonalResidual K z := by
    rw [map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le hCA]
    rfl
  have hs : (Source.orthogonalResidual K z).subgroupOf A =
      (primeToResidual 3 C).map C.subtype := by
    apply map_injective A.subtype_injective
    rw [he]
    exact map_subgroupOf_eq_of_le ((map_subtype_le _).trans hCA)
  change ((Source.orthogonalResidual K z).subgroupOf A).map _ = _
  rw [hs, map_embedded_primeToResidual_of_hom]
  rfl

/-- The residual image uses the stabilizer of the very same seed z. -/
theorem plusImage_residual_seed :
    plusImage K L T z v hL hz (Source.orthogonalResidual K z) =
      (primeToResidual 3 (plusImage K L T z v hL hz K ⊓
        seedStabilizer K L T z v hL hz : Subgroup _)).map
        (plusImage K L T z v hL hz K ⊓ seedStabilizer K L T z v hL hz).subtype := by
  rw [plusImage_orthogonalResidual, plusImage_centralizer]

/-- Core images retain the literal subgroup inclusion in G and the plus map. -/
theorem plusImage_pCoreIn (H : Subgroup G) (hH : H ≤ plusActor K L T v)
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker) :
    plusImage K L T z v hL hz (H.pCoreIn 2) =
      (plusImage K L T z v hL hz H).pCoreIn 2 := by
  have hs : (H.pCoreIn 2).subgroupOf (plusActor K L T v) =
      (H.subgroupOf (plusActor K L T v)).pCoreIn 2 := by
    apply map_injective (plusActor K L T v).subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 H).trans hH),
      map_pCoreIn_of_injective 2 _ _ (plusActor K L T v).subtype_injective,
      map_subgroupOf_eq_of_le hH]
  change ((H.pCoreIn 2).subgroupOf _).map _ = _
  rw [hs, map_pCoreIn_of_ker_isPGroup _ hk]
  rfl

/-- Apply the core-image calculation to the source group XTᵥ. -/
theorem residual_join_core_image
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker) :
    plusImage K L T z v hL hz
      ((Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2) =
      (plusImage K L T z v hL hz (Source.orthogonalResidual K z) ⊔
        plusImage K L T z v hL hz (Tv T v)).pCoreIn 2 := by
  have hX : Source.orthogonalResidual K z ≤ plusActor K L T v :=
    (map_subtype_le _).trans (inf_le_left.trans (K_le_plusActor K L T v))
  rw [plusImage_pCoreIn K L T z v hL hz _ (sup_le hX le_sup_right) hk,
    plusImage_sup K L T z v hL hz _ _ hX le_sup_right]

/-- An equivariant marking of the original seed transports the actual residual
into the even four-block group. The geometric marking is not inferred from dimension. -/
theorem residual_image_of_seed_marking
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (hC : (plusImage K L T z v hL hz K).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hseed : (seedStabilizer K L T z v hL hz).map e.toMonoidHom =
      A6ShadowTwoLocals.fourStabilizer) :
    (plusImage K L T z v hL hz (Source.orthogonalResidual K z)).map e.toMonoidHom =
      (primeToResidual 3 (alternatingGroup (Fin 8) ⊓
        A6ShadowTwoLocals.fourStabilizer : Subgroup _)).map
        (alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer).subtype := by
  rw [plusImage_residual_seed, map_embedded_primeToResidual_of_hom,
    Subgroup.map_inf _ _ _ e.injective, hC, hseed]

/-- The actual Rᵥ maps to the two block Klein-four groups once the XTᵥ image
is the four-block stabilizer. This is the core needed by the Thompson comparison. -/
theorem residual_join_core_model
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker)
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (himage : (plusImage K L T z v hL hz
      (Source.orthogonalResidual K z ⊔ Tv T v)).map e.toMonoidHom =
        A6ShadowTwoLocals.fourStabilizer) :
    (plusImage K L T z v hL hz
      ((Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2)).map e.toMonoidHom =
        FourBlockCoreAction.kleinGroup := by
  have hX : Source.orthogonalResidual K z ≤ plusActor K L T v :=
    (map_subtype_le _).trans (inf_le_left.trans (K_le_plusActor K L T v))
  rw [plusImage_pCoreIn K L T z v hL hz _ (sup_le hX le_sup_right) hk,
    map_pCoreIn_of_injective 2 _ _ e.injective, himage,
    FourBlockCoreAction.fourStabilizer_pCoreIn]

/-- The literal XTᵥ quotient, before choosing a model for its plus image. -/
noncomputable def residualJoinQuotientEquiv
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker) :
    (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G) ⧸
        pCore 2 (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G) ≃*
      (plusImage K L T z v hL hz (Source.orthogonalResidual K z ⊔ Tv T v)) ⧸
        pCore 2 (plusImage K L T z v hL hz (Source.orthogonalResidual K z ⊔ Tv T v)) := by
  have hX : Source.orthogonalResidual K z ≤ plusActor K L T v :=
    (map_subtype_le _).trans (inf_le_left.trans (K_le_plusActor K L T v))
  exact (imageProjection K L T z v hL hz _ (sup_le hX le_sup_right)).pCoreQuotientEquiv
    (imageProjection_surjective K L T z v hL hz _ _)
    (imageProjection_kernel K L T z v hL hz _ _ hk)

/-- The quotient equivalence uses the same plus quotient on every representative. -/
theorem residualJoinQuotientEquiv_mk
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker)
    (x : (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G)) :
    residualJoinQuotientEquiv K L T z v hL hz hk (QuotientGroup.mk x) =
      QuotientGroup.mk
        (imageProjection K L T z v hL hz _
          (sup_le ((map_subtype_le _).trans
            (inf_le_left.trans (K_le_plusActor K L T v))) le_sup_right) x) := rfl

/-- The marked image equivalence induces the concrete four-block quotient.
The source assembly must still construct its image equality. -/
noncomputable def fourBlockQuotientEquiv
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker)
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (himage : (plusImage K L T z v hL hz
      (Source.orthogonalResidual K z ⊔ Tv T v)).map e.toMonoidHom =
        A6ShadowTwoLocals.fourStabilizer) :
    (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G) ⧸
      pCore 2 (Source.orthogonalResidual K z ⊔ Tv T v : Subgroup G) ≃*
        A6ShadowTwoLocals.fourStabilizer ⧸ pCore 2 A6ShadowTwoLocals.fourStabilizer :=
  (residualJoinQuotientEquiv K L T z v hL hz hk).trans
    (let eH := (e.subgroupMap (plusImage K L T z v hL hz
      (Source.orthogonalResidual K z ⊔ Tv T v))).trans (MulEquiv.subgroupCongr himage)
     QuotientGroup.congr _ _ eH (pCore_map_iso 2 eH))

end Finite
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
