module
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalImage
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedSection
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryPermutation
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryConjugationSection
/-!
# The original deleted-five section in the A₇ point-action row

The actual local A₅ quotient in the containing component acts on the
six-dimensional deleted A₇ module. Its moved space is the marked deleted
five-letter module. The original factor W is contained in this space because
W = [W,L]; its order is at least sixteen, so it fills the four-dimensional
moved space. The resulting conjugation coordinates retain the original L,
W and quotient marking, with trivial kernel.

Source: Aschbacher–Smith, 10.2.9, printed pp.751–752. The larger orbit VI
need not lie in the original full module; only the proved containment W ≤ VI
and full movement of W are used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterB.InternalThompsonAction BinaryPermutation

private theorem section_of_original_moved_coordinates
    {G : Type*} [Group G] [Finite G]
    (H L W : Subgroup G) (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hLH : L ≤ H) (hWH : W ≤ H) (hWU : W.subgroupOf H ≤ U)
    (hWL : W ≤ L) (hnorm : L ≤ normalizer (W : Set G))
    (hmove : ⁅W,L⁆ = W) (hcard : 16 ≤ Nat.card W)
    (τ : Representation (ZMod 2) L (natural (Fin 5)))
    (E : subspaceCommutator (NormalElementaryQuotient.representation U (actionMk U)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ ((L.subgroupOf H).map (actionMk U)) ≃ₗ[ZMod 2]
      natural (Fin 5))
    (hE : ∀ (l : L) v,
      (E.symm (τ l v) : Additive U) =
        NormalElementaryQuotient.representation U (actionMk U)
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (actionMk U ⟨l,hLH l.property⟩) (E.symm v)) :
    Nonempty (BinaryConjugationSection L W ⊥ τ) := by
  let J := L.subgroupOf H
  let C := ⁅U,J⁆
  have hCU : C ≤ U := commutator_le_left _ _
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCU) (inclusion_injective hCU)
  let EC := (NormalElementaryQuotient.movedEquiv U (actionMk U)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) J).trans E
  have hCcard : Nat.card C = 16 := by
    change Nat.card (Additive C) = 16
    rw [Nat.card_congr EC.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, finrank_natural_odd (Fin 5) (by decide)]
    decide
  have hWcomm : ⁅W.subgroupOf H,J⁆ = W.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hWH,
      map_subgroupOf_eq_of_le hLH, hmove]
  have hWC : W.subgroupOf H ≤ C :=
    hWcomm.symm.le.trans (commutator_mono hWU le_rfl)
  have hWeq : W.subgroupOf H = C := eq_of_le_of_card_ge hWC (by
    rw [hCcard, Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv]
    exact hcard)
  let k : W ≃* C := (subgroupOfEquivOfLe hWH).symm.trans (MulEquiv.subgroupCongr hWeq)
  let c : W →* Multiplicative (natural (Fin 5)) := {
    toFun w := Multiplicative.ofAdd (EC (Additive.ofMul (k w)))
    map_one' := by simp
    map_mul' a b := by
      apply Multiplicative.toAdd.injective
      change EC (Additive.ofMul (k (a*b))) = EC (Additive.ofMul (k a)) + EC (Additive.ofMul (k b))
      rw [k.map_mul]
      exact EC.map_add _ _ }
  have hcoords (w : W) : (E.symm (c w).toAdd : Additive U) =
      Additive.ofMul (⟨⟨w,hWH w.property⟩,hWU w.property⟩ : U) := by
    change (E.symm (E ((NormalElementaryQuotient.movedEquiv U (actionMk U)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) J)
        (Additive.ofMul (k w))))).val = _
    rw [E.symm_apply_apply]
    rfl
  have hc : Function.Bijective c := by
    constructor
    · intro a b hab
      apply k.injective
      apply Additive.ofMul.injective
      apply EC.injective
      exact congrArg Multiplicative.toAdd hab
    · intro v
      exact ⟨k.symm (EC.symm v.toAdd).toMul, by
        apply Multiplicative.toAdd.injective
        change EC (Additive.ofMul (k (k.symm (EC.symm v.toAdd).toMul))) = v.toAdd
        rw [k.apply_symm_apply, ofMul_toMul, EC.apply_symm_apply]⟩
  refine ⟨{
    section_le := hWL
    kernel_le := bot_le
    normalized := hnorm
    coordinates := c
    onto := hc.2
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · rw [(MonoidHom.ker_eq_bot_iff c).mpr hc.1, bot_subgroupOf]
  · intro l w
    apply E.symm.injective
    apply Subtype.val_injective
    rw [hE, hcoords, hcoords]
    change Additive.ofMul (⟨⟨(l:G)*(w:G)*(l:G)⁻¹,_⟩,_⟩ : U) =
      NormalElementaryQuotient.representation U (actionMk U)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (actionMk U ⟨l,hLH l.property⟩) (Additive.ofMul (⟨⟨w,hWH w.property⟩,_⟩ : U))
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U (actionMk U)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      ⟨l,hLH l.property⟩ (Additive.ofMul (⟨⟨w,hWH w.property⟩,hWU w.property⟩ : U))).symm

open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Original deleted-five coordinates from the literal A₇ action on the point orbit. -/
theorem source_a5_point_deleted_five
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf H
    letI := hr.normal
    letI := hr.elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (eA : A ≃* alternatingGroup (Fin 7))
      (F : Additive U ≃ₗ[ZMod 2] natural (Fin 7)),
      (∀ (a : A) w, F (action U a.val w) = alternatingNaturalRepresentation (Fin 7) (eA a) (F w)) →
      Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((alternatingNaturalRepresentation (Fin 5)).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I
  let U := V.subgroupOf H
  let := hr.normal
  let := hr.elementary
  let K := I.subgroupOf H
  let J := L.subgroupOf H
  let B := J.subgroupOf K
  let q := actionMk U
  let A := K.map q
  dsimp only
  intro eA F hF
  have hLH : L ≤ H := hLI.trans le_sup_left
  have hJK : J ≤ K := comap_mono hLI
  have hHX : H ≤ centralizer ({v} : Set G) := sup_le hIX inf_le_right
  obtain ⟨P,hP⟩ := hs.restrict le_sup_right hHX
  have hP' : (P : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hJlocal : J ∈ localCComponents P := by
    rw [hP']
    exact ChapterA.Section03.SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) hLH
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans hNI))
  obtain ⟨R,_,hBR⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hJlocal hJK (inferInstance : K.Normal).isSubnormal
  let f := eA.toMonoidHom.comp (q.subgroupMap K)
  have hf : Function.Surjective f := eA.surjective.comp (q.subgroupMap_surjective K)
  have hfker : f.ker = (q.subgroupMap K).ker := by
    ext k
    change eA ((q.subgroupMap K) k) = 1 ↔ (q.subgroupMap K) k = 1
    exact map_eq_one_iff eA eA.injective
  have hks : Group.IsSolvable f.ker := by
    rw [hfker]
    exact source_a5_point_component_action_kernel_solvable D I hLI hIX hI hout hCW hspan hr
  let kJ : B ≃* J := subgroupOfEquivOfLe hJK
  let kL : B ≃* L := kJ.trans (subgroupOfEquivOfLe hLH)
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ kL (pCore_map_iso 2 kL)).trans e
  have hkerB : (f.subgroupMap B).ker = ((q.subgroupMap J).ker).comap kJ.toMonoidHom := by
    ext b
    change (f.subgroupMap B) b = 1 ↔ (q.subgroupMap J) (kJ b) = 1
    constructor
    · intro hb
      apply Subtype.ext
      have hh : eA ((q.subgroupMap K) b.val) = 1 := congrArg Subtype.val hb
      have hh' := (map_eq_one_iff eA eA.injective).mp hh
      exact congrArg (fun z : K.map q => z.val) hh'
    · intro hb
      apply Subtype.ext
      change eA ((q.subgroupMap K) b.val) = 1
      apply (map_eq_one_iff eA eA.injective).mpr
      apply Subtype.ext
      exact congrArg (fun z : J.map q => z.val) hb
  have hk : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [hkerB]
    exact (source_a5_point_small_image_twoCore D e I hLI hout hCW hspan hr).1.comap_of_injective
      kJ.toMonoidHom kJ.injective
  let ρ := (action U).comp (q.comp K.subtype)
  obtain ⟨E,hE⟩ := ChapterA.Section03.SourceEmbeddings.alternatingSeven_five_section_moved_equiv_of_equivariant
    f hf hks R B hBR hk eB ρ F (fun k w => hF ((q.subgroupMap K) k) w)
  have himage : B.map (q.comp K.subtype) = J.map q := by
    rw [←map_map, map_subgroupOf_eq_of_le hJK]
  have hm : subspaceCommutator ρ ⊤ B = subspaceCommutator (action U) ⊤ (J.map q) := by
    rw [subspaceCommutator_comp_map,himage]
  let E' := (LinearEquiv.ofEq _ _ hm.symm).trans E
  have hE' (l : L) (w : natural (Fin 5)) :
      (E'.symm (alternatingNaturalRepresentation (Fin 5) (e (QuotientGroup.mk' (pCore 2 L) l)) w) : Additive U) =
        action U (q ⟨l,hLH l.property⟩) (E'.symm w) := by
    have hh := hE (kL.symm l) w
    change (E.symm (alternatingNaturalRepresentation (Fin 5)
      (e (QuotientGroup.mk' (pCore 2 L) (kL (kL.symm l)))) w) : Additive U) = _ at hh
    rw [kL.apply_symm_apply] at hh
    exact hh
  have hWH : ⁅D.fullModule,L⁆ ≤ H := (source_full_moved_le_component D).trans hLH
  exact section_of_original_moved_coordinates H L ⁅D.fullModule,L⁆ U hLH hWH
    (comap_mono hspan) (source_full_moved_le_component D)
    (normalizer_commutator_ge_right _ _) (source_full_moved_eq_commutator D)
    (source_a5_full_moved_card D e) _ E' hE'

end CFSG.Quasithin.Chapter10
