module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2Affine
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.PCoreSurjective
public import Theory.ElementaryAbelian.AbelianNormalClosure
/-!
# Non-shortness from the literal elementary action

For a perfect short group, irreducibility of its commutator module forces
the two-core part of an action kernel to be central whenever the image of
that commutator module is noncentral. Apply this to [W_K,R]: mutual
normalization places this elementary subgroup inside O₂(R), and abelianness
of W_K puts it in the action kernel. Perfectness would then force R to
centralize W_K, contrary to movement of z.

For either published SL₃ parabolic preimage, the actual plus image of R is
an affine SL₂ group. Its core commutator is noncentral. The two-group kernel
needed to lift that core is explicit and belongs to the independent
LocalStructure producer. W_K-normalization of every preimage is proved
from W_K ≤ Tᵥ and Tᵥ-normalization of K; no local membership or invariance
of the parabolic under all of Tᵥ is assumed.

This proves the required non-shortness using C.1.7's irreducibility clause.
It does not assert the stronger nonzero core triple commutator: failure of
shortness need not violate C.1.7's centrality clause. The separate marked
module calculation must still exclude graph interchange to give full
Tᵥ-invariance. Earlier elementary and ambient-core placement remain with
qt-13-06-centralizer-reduction; final SL₃ assembly remains with
qt-13-06-higher-field-sl3-parabolics.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.19, printed p.931, and C.1.7, printed p.123.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection
universe u
variable {G : Type u} [Group G]

private theorem map_center_le_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) : (center A).map f ≤ center B := by
  rintro _ ⟨a, ha, rfl⟩
  apply mem_center_iff.mpr
  intro b
  obtain ⟨x, rfl⟩ := hf b
  exact (map_mul f x a).symm.trans ((congrArg f (mem_center_iff.mp ha x)).trans
    (map_mul f a x))

/-- Irreducibility in C.1.7 forces the core part of the kernel of a
surjection to be central when its commutator image is noncentral. -/
theorem kernel_core_central_of_short {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] (f : A →* B) (hf : Function.Surjective f)
    (hi : ¬ (ChapterC.blockU A).map f ≤ center B) (hs : ChapterC.IsShort A) :
    pCore 2 A ⊓ f.ker ≤ center A := by
  let U := ChapterC.blockU A
  let Z := U ⊓ center A
  let N := (U ⊓ f.ker) ⊔ Z
  have hN : N ≤ U := sup_le inf_le_left inf_le_left
  have hne : N ≠ U := by
    intro he
    apply hi
    change U.map f ≤ center B
    rw [← he, Subgroup.map_sup]
    apply sup_le
    · exact (map_mono (show U ⊓ f.ker ≤ f.ker from inf_le_right)).trans
        (by rw [Subgroup.map_ker_self]; exact bot_le)
    · exact (map_mono (show Z ≤ center A from inf_le_right)).trans
        (map_center_le_of_surjective f hf)
  have hn : N.Normal := inferInstance
  have he : N = Z := (hs.irreducible.2 N hn le_sup_right hN).resolve_right hne
  have hcomm : ⁅pCore 2 A ⊓ f.ker, (⊤ : Subgroup A)⁆ ≤ center A := by
    have hh : ⁅pCore 2 A ⊓ f.ker, (⊤ : Subgroup A)⁆ ≤ U ⊓ f.ker :=
      le_inf (commutator_mono inf_le_left le_rfl)
        ((commutator_mono inf_le_right le_rfl).trans (commutator_le_left _ _))
    exact hh.trans ((le_sup_left.trans he.le).trans inf_le_right)
  apply commutator_top_right_eq_bot_iff_le_center.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  exact commutator_top_right_eq_bot_iff_le_center.mpr hcomm

/-- If the action on an elementary abelian subgroup has noncentral core
commutator image, a moving perfect subgroup cannot be short. Both mutual
normalizations retain the original ambient embeddings. -/
theorem not_short_of_action_image [Finite G] (R W : Subgroup G)
    [Group.IsPerfect R] [IsElementaryAbelian 2 W]
    (hRW : R ≤ normalizer (W : Set G)) (hWR : W ≤ normalizer (R : Set G))
    (hm : ⁅W, R⁆ ≠ ⊥)
    {D : Type*} [Group D] (f : R →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (W : Set G)).subgroupOf R)
    (hi : ¬ (ChapterC.blockU R).map f ≤ center D) : ¬ ChapterC.IsShort R := by
  intro hs
  let M := ⁅W, R⁆
  have hMW : M ≤ W := le_normalizer_iff_commutator_le_left.mp hRW
  have hMR : M ≤ R := le_normalizer_iff_commutator_le_right.mp hWR
  have hMC : M ≤ centralizer (W : Set G) := by
    have hh : ⁅W, W⁆ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance
    exact hMW.trans (commutator_eq_bot_iff_le_centralizer.mp hh)
  have hcore : M ≤ R.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 W).to_le hMW) hMR
      (normalizer_commutator_ge_right W R)
  have hM : M.subgroupOf R ≤ pCore 2 R ⊓ f.ker := by
    apply le_inf
    · change M.comap R.subtype ≤ pCore 2 R
      have hh := comap_mono (f := R.subtype) hcore
      simpa only [pCoreIn, comap_map_eq_self_of_injective R.subtype_injective] using hh
    · rw [hk]
      exact comap_mono hMC
  have hc := hM.trans (kernel_core_central_of_short f hf hi hs)
  have hh := congrArg (Subgroup.map R.subtype)
    (commutator_top_right_eq_bot_iff_le_center.mpr hc)
  rw [map_commutator, map_subgroupOf_eq_of_le hMR,
    ← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] at hh
  exact hm (commutator_eq_bot_of_iterated_eq_bot W R hh)

/-- The affine quotient supplies the noncentral image intrinsically.
Only its actual action kernel being a two-group remains a local input. -/
theorem not_short_of_affine_action [Finite G] (R W : Subgroup G)
    [Group.IsPerfect R] [IsElementaryAbelian 2 W]
    (hRW : R ≤ normalizer (W : Set G)) (hWR : W ≤ normalizer (R : Set G))
    (hm : ⁅W, R⁆ ≠ ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (f : R →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (W : Set G)).subgroupOf R)
    (hp : IsPGroup 2 f.ker) : ¬ ChapterC.IsShort R := by
  apply not_short_of_action_image R W hRW hWR hm f hf hk
  have hcore : (pCore 2 R).map f = pCore 2 (Matrix.SL2.Affine F) := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hp, map_comap_eq_self_of_surjective hf]
  have he : (ChapterC.blockU R).map f = pCore 2 (Matrix.SL2.Affine F) := by
    rw [ChapterC.blockU, map_commutator, hcore, map_top_of_surjective f hf]
    exact ChapterC.SL2Affine.blockU_eq_core (MulEquiv.refl _)
  rw [he]
  exact ChapterC.SL2Affine.core_not_le_center (MulEquiv.refl _)

/-- An element centralizing W_K acts trivially on its literal plus quotient.
Consequently W_K normalizes every model preimage, independently of whether
Tᵥ normalizes that preimage. -/
theorem WK_normalizes_preimage
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    {D : Type*} [Group D]
    (e : plusImage K L T z v hL hz K ≃* D) (P : Subgroup D) :
    WK K L T z v ≤ normalizer
      (preimageIn K (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P : Set G) := by
  let A := plusActor K L T v
  let q := plusMk K L T z v hL hz
  let c := componentPlusMap K L T z v hL hz
  have hWC : WK K L T z v ≤ centralizer (WK K L T z v : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_self_eq_bot_iff.mpr inferInstance)
  apply le_normalizer_iff.mpr
  intro w hw x hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hwa : w ∈ A := (show Tv T v ≤ A from le_sup_right) (hW hw)
  let a : A := ⟨w, hwa⟩
  have ha : q a = 1 := by
    change a ∈ q.ker
    rw [plusMk_ker]
    exact hWC hw
  have hconj : w * (k : G) * w⁻¹ ∈ K :=
    (mem_normalizer_iff.mp (hn (hW hw)) k).mp k.property
  let k' : K := ⟨w * k * w⁻¹, hconj⟩
  have hc : c k' = c k := by
    apply Subtype.ext
    change q (a * inclusion (K_le_plusActor K L T v) k * a⁻¹) =
      q (inclusion (K_le_plusActor K L T v) k)
    simp only [map_mul, map_inv, ha, one_mul, inv_one, mul_one]
  exact mem_map.mpr ⟨k', by change e (c k') ∈ P; rw [hc]; exact hk, rfl⟩

/-- The action epimorphism of the embedded residual, using its original
plus map. Its kernel is the relative centralizer of W_K. -/
def residualPlusMap (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hP : P ≤ K) :
    residualIn P →* plusImage K L T z v hL hz (residualIn P) :=
  ((plusMk K L T z v hL hz).comp
    (inclusion (((map_subtype_le _).trans hP).trans (K_le_plusActor K L T v)))).codRestrict _
      (fun x => mem_map.mpr ⟨⟨x, ((map_subtype_le _).trans hP).trans
        (K_le_plusActor K L T v) x.property⟩, x.property, rfl⟩)

theorem residualPlusMap_surjective (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hP : P ≤ K) :
    Function.Surjective (residualPlusMap K L T P z v hL hz hP) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

theorem residualPlusMap_ker (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hP : P ≤ K) :
    (residualPlusMap K L T P z v hL hz hP).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf (residualIn P) := by
  ext x
  change residualPlusMap K L T P z v hL hz hP x = 1 ↔ _
  rw [Subtype.ext_iff]
  change inclusion _ x ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

/-- The non-shortness obstruction for a moving literal parabolic preimage.
The intrinsic action kernel being a two-group is the local-structure input.
The proof uses irreducibility of the short-group commutator module. -/
theorem moving_preimage_not_short [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    {D : Type*} [Group D]
    (e : plusImage K L T z v hL hz K ≃* D) (P : Subgroup D)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : residualIn P ≃* Matrix.SL2.Affine F)
    (hm : ¬ residualIn (preimageIn K
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P) ≤
        centralizer ({z} : Set G))
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf
      (residualIn (preimageIn K
        (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P)))) :
    ¬ ChapterC.IsShort (residualIn (preimageIn K
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P)) := by
  let P' := preimageIn K (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P
  let R := residualIn P'
  have hPK : P' ≤ K := preimageIn_le _ _ _
  have hRK : R ≤ K := (map_subtype_le _).trans hPK
  let c := residualPlusMap K L T P' z v hL hz hPK
  let b := (plusResidualEquiv K L T z v hL hz e P).trans a
  let f := b.toMonoidHom.comp c
  have hfk : f.ker = (centralizer (WK K L T z v : Set G)).subgroupOf R := by
    change (b.toMonoidHom.comp c).ker = _
    rw [MonoidHom.ker_comp_of_injective c b.toMonoidHom b.injective]
    exact residualPlusMap_ker K L T P' z v hL hz hPK
  have hm' : ⁅WK K L T z v, R⁆ ≠ ⊥ := by
    intro he
    apply hm
    exact (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm R (WK K L T z v)).trans he)).trans
        (centralizer_le (Set.singleton_subset_iff.mpr
          (le_conjugateSpanBy _ _ (mem_zpowers z))))
  let : Group.IsPerfect R := Group.IsPerfect.map P'.subtype
  exact not_short_of_affine_action R (WK K L T z v)
    (hRK.trans ((K_le_plusActor K L T v).trans
      (plusActor_normalizes_WK K L T z v hL hz)))
    (residualIn_normalized _ P' (WK_normalizes_preimage K L T z v hL hz hW hn e P))
    hm' f (b.surjective.comp (residualPlusMap_surjective K L T P' z v hL hz hPK))
    hfk (hfk.symm ▸ hk)


/-- The source ambient core placement puts W_K in the actual Sylow Tᵥ. -/
theorem WK_le_Tv_of_ambient_core (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hS : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) : WK K L T z v ≤ Tv T v := by
  obtain ⟨S, hS⟩ := hS
  exact (WK_le_Uv K L T z v hK).trans (hU.trans ((pCoreIn_le_sylow _ S).trans_eq hS))

open scoped MatrixGroups

/-- Application to the published point and line preimages under the same
aligned equivalence. All natural, dual, repeated and extension alternatives
are allowed because the proof uses only the faithful abelian action. -/
theorem flag_residual_not_short [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (P : Subgroup G)
    (hP : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
    (hm : ¬ residualIn P ≤ centralizer ({z} : Set G))
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf (residualIn P))) :
    ¬ ChapterC.IsShort (residualIn P) := by
  rcases hP with hP | hP
  · subst P
    exact moving_preimage_not_short K L T z v hL hz hW hn e
      (Matrix.PSL3.LinearThree.pointParabolicSL F)
      ((MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.pointParabolicSL_residual F hcard)).trans
        (Matrix.PSL3.LinearThree.pointLocalAffineEquiv F)) hm hk
  · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp hP
    subst P
    exact moving_preimage_not_short K L T z v hL hz hW hn e
      (Matrix.PSL3.LinearThree.lineParabolicSL F)
      ((MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.lineParabolicSL_residual F hcard)).trans
        (Matrix.PSL3.LinearThree.lineLocalAffineEquiv F)) hm hk

/-- The actual movement selection supplies a non-short residual. No moving
witness or assertion of non-blockness is an input. The remaining intrinsic
kernel premise has exactly the relative-centralizer embedding used above. -/
theorem exists_moving_nonshort_flag [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (Uv z v)]
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hS : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
        Matrix.PSL3.LinearThree.unipotentSL F)
    (hk : ∀ P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
      IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf (residualIn P))) :
    ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = (2 : ℕ) ^ 2 by decide).le.trans
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hm)
  obtain ⟨P, hP, hPK, hmax, hTP, hmove, _⟩ :=
    moving_marked_flag_residual F hm hF K L T z v hL hz hK hn e hmark
  exact ⟨P, hP, hPK, hmax, hTP, hmove,
    flag_residual_not_short hcard K L T z v hL hz
      (WK_le_Tv_of_ambient_core K L T z v hK.1.1 hU hS) hn e P hP hmove (hk P hP)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
