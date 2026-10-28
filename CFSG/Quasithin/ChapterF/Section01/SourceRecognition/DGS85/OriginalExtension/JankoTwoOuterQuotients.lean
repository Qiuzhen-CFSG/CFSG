module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoParabolics
public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Sign
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Sylow

/-!
# Original outer Hall–Janko quotient actions

For a proper extension of a genuinely marked reduced J₂ pair, the full
second endpoint has order 2304 and unchanged two-core of order 64. Its
core quotient is S₃ × S₃: the characteristic S₃ factor of the normal
reduced quotient S₃ × C₃ splits off, and its core-free order-six
centralizer is S₃. The resulting equivalence retains the literal reduced
quotient map, including an injective marking of the odd C₃ factor.

The original Sylow image is an elementary four-group. The whole original
Borel modulo its own two-core is S₃; the reduced Borel is precisely the
preimage of A₃. Thus every outer Borel actor inverts the reduced odd
quotient. These results use finite stabilizers only and work in either
endpoint orientation. They do not lift a quotient involution to an actual
involution or identify the original parabolics from their orders.

This advances the proper-extension argument in DGS, Groups and Graphs
(1985), (15.3), pp.229–231. The source's alpha endpoint is the repository's
second endpoint; its beta endpoint is the first. The remaining normalizer
and outer-generator relations are required for Aut(J₂) recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
local notation "S3" => Equiv.Perm (Fin 3)
local notation "C3" => Multiplicative (ZMod 3)

private theorem s3_cubic_hom_trivial (f : S3 →* C3) (x : S3) : f x = 1 := by
  have hk : f.ker = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.closure_isSwap, closure_le]
    rintro y ⟨a,b,_,rfl⟩
    have he : f (Equiv.swap a b) ^ 2 = 1 := by rw [← map_pow]; simp [pow_two]
    exact (show ∀ z : C3, z ^ 2 = 1 → z = 1 by decide +kernel) _ he
  change x ∈ f.ker
  rw [hk]
  trivial

private abbrev firstFactor : Subgroup (S3 × C3) := (MonoidHom.snd S3 C3).ker

private theorem firstFactor_characteristic : firstFactor.Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  have hx' : x.2 = 1 := hx
  have hh := s3_cubic_hom_trivial
    ((MonoidHom.snd S3 C3).comp (a.toMonoidHom.comp (MonoidHom.inl S3 C3))) x.1
  change (a x).2 = 1
  change (a (x.1,1)).2 = 1 at hh
  simpa only [← hx',Prod.mk.eta] using hh

private def firstFactorEquiv : firstFactor ≃* S3 where
  toFun x := x.val.1
  invFun x := ⟨(x,1),rfl⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext rfl x.property.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem characteristic_map_equiv {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (K : Subgroup A) [K.Characteristic] :
    (K.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y,hy,rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

private theorem symmetric_three_of_six {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A = 6) (hq : pCore 2 A = ⊥) : Nonempty (A ≃* S3) := by
  let T : Sylow 2 A := Classical.choice inferInstance
  have hT : Nat.card T = 2 := by rw [T.card_eq_multiplicity,hc]; decide +kernel
  have hi : (T : Subgroup A).index = 3 := by
    have hh := (T : Subgroup A).card_mul_index
    rw [hT,hc] at hh
    omega
  let f := MulAction.toPermHom A (A ⧸ (T : Subgroup A))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← normalCore_eq_ker]
    apply bot_unique
    rw [← hq]
    exact le_sSup ⟨inferInstance,
      T.isPGroup'.of_injective (inclusion (normalCore_le _)) (inclusion_injective _)⟩
  let := Fintype.ofFinite (A ⧸ (T : Subgroup A))
  let e := Fintype.equivFinOfCardEq (show Fintype.card (A ⧸ (T : Subgroup A)) = 3 by
    rw [← Nat.card_eq_fintype_card]; exact hi)
  let g : A →* S3 := (Equiv.permCongrHom e).toMonoidHom.comp f
  have hg : Function.Injective g := (Equiv.permCongrHom e).injective.comp hf
  exact ⟨MulEquiv.ofBijective g (hg.bijective_of_nat_card_le (by
    rw [hc,Nat.card_perm,Nat.card_fin]; decide))⟩

/-- The core-free order-36 extension of the reduced second quotient has
both symmetric-three factors. The normal reduced subgroup is literal. -/
private theorem second_quotient_extension_marked {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A = 36) (hq : pCore 2 A = ⊥)
    (J : Subgroup A) [J.Normal] (e : J ≃* (S3 × C3)) :
    ∃ d : A ≃* (S3 × S3), ∃ c : C3 →* S3,
      Function.Injective c ∧ ∀ x : J, d x = ((e x).1,c (e x).2) := by
  let F := firstFactor.map e.symm.toMonoidHom
  let : firstFactor.Characteristic := firstFactor_characteristic
  let : F.Characteristic := characteristic_map_equiv e.symm firstFactor
  let I := F.map J.subtype
  let : I.Normal := ConjAct.normal_of_characteristic_of_normal
  let eI : I ≃* S3 := ((F.equivMapOfInjective J.subtype J.subtype_injective).symm.trans
    (e.symm.subgroupMap firstFactor).symm).trans firstFactorEquiv
  let C := centralizer (I : Set A)
  obtain ⟨d,hd⟩ := NormalSymmetricThree.exists_product_equiv I eI
  have hI : Nat.card I = 6 := by rw [Nat.card_congr eI.toEquiv,Nat.card_perm,Nat.card_fin]; rfl
  have hC : Nat.card C = 6 := by
    have hh := Nat.card_congr d.toEquiv
    rw [Nat.card_prod,hI,hc] at hh
    change 6 * Nat.card C = 36 at hh
    omega
  have hcore : pCore 2 C = ⊥ := by
    apply ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    apply bot_unique
    rw [← hq]
    exact le_sSup ⟨by dsimp [C]; infer_instance,pCore_isPGroup.map _⟩
  obtain ⟨eC⟩ := symmetric_three_of_six hC hcore
  let f := d.symm.trans (eI.prodCongr eC)
  let emb : S3 × C3 →* A := J.subtype.comp e.symm.toMonoidHom
  have hf (s : S3) : f (emb (s,1)) = (s,1) := by
    let z : I := eI.symm s
    have hz : (z : A) = emb (s,1) := rfl
    have hh := hd z 1
    rw [coe_one,mul_one,hz] at hh
    change (eI.prodCongr eC) (d.symm (emb (s,1))) = _
    rw [← hh,d.symm_apply_apply]
    change (eI (eI.symm s),eC 1) = (s,1)
    rw [eI.apply_symm_apply,map_one]
  let c : C3 →* S3 := (MonoidHom.snd S3 S3).comp
    (f.toMonoidHom.comp (emb.comp (MonoidHom.inr S3 C3)))
  have hcfirst (z : C3) : (f (emb (1,z))).1 = 1 := by
    apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
    intro y
    have hh : emb (y,1) * emb (1,z) = emb (1,z) * emb (y,1) := by
      rw [← map_mul,← map_mul]
      simp
    have hh' := congrArg (fun x => (f x).1) hh
    simpa only [map_mul,hf,Prod.fst_mul] using hh'
  have hcz (z : C3) : f (emb (1,z)) = (1,c z) := Prod.ext (hcfirst z) rfl
  have hci : Function.Injective c := by
    intro z w hh
    have heq : f (emb (1,z)) = f (emb (1,w)) := by rw [hcz,hcz,hh]
    have hi : Function.Injective emb := J.subtype_injective.comp e.symm.injective
    exact congrArg Prod.snd (hi (f.injective heq))
  refine ⟨f,c,hci,fun x => ?_⟩
  have hx : (x : A) = emb ((e x).1,1) * emb (1,(e x).2) := by
    rw [← map_mul]
    simp only [Prod.mk_mul_mk,mul_one,one_mul]
    exact congrArg Subtype.val (e.symm_apply_apply x).symm
  rw [hx,map_mul,hf,hcz]
  simp

open SuzukiContainment GreenBook
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The second full original parabolic doubles the reduced order 1152. -/
theorem original_second_card_of_ne (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) : Nat.card (parabolic L S j) = 2304 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    (parabolic L (reducedSylow L S) j) (parabolic L S j) bot_le (reduced_parabolic_le h j)
  have hr : Nat.card (parabolic L (reducedSylow L S) j) = 1152 :=
    (Nat.card_congr (f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one)).toEquiv).trans
      PairNormalizer.card_p₂
  rw [relIndex_bot_left,relIndex_bot_left,hr,parabolic_extension_index h j,
    original_borel_index_two_of_ne h i e hne] at hc
  exact hc.symm

private theorem quotientMap_range_normal (h : HypothesisF11 L S) (j : Fin 2) :
    (coreQuotientMap h j).range.Normal := by
  let q := QuotientGroup.mk' (pCore 2 (parabolic L S j))
  let r := QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))
  have he : (coreQuotientMap h j).comp r = q.comp (inclusion (reduced_parabolic_le h j)) := by
    ext x
    exact coreQuotientMap_mk h j x
  have hr : ((coreQuotientMap h j).comp r).range = (coreQuotientMap h j).range := by
    rw [MonoidHom.range_comp,r.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  rw [← hr,he,MonoidHom.range_comp,inclusion_range]
  exact (reduced_parabolic_normal h j).map q (QuotientGroup.mk'_surjective _)

/-- Concrete coordinates on the reduced second core quotient. -/
@[expose] def reducedSecondQuotientEquiv (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    (parabolic L (reducedSylow L S) j ⧸ pCore 2 (parabolic L (reducedSylow L S) j)) ≃*
      (S3 × C3) :=
  (LocalCoreTransport.quotientEquiv 2
    (f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one))).trans
      (PairNormalizer.p₂_core_and_quotient SecondParabolic.l₂_core_card).2.some

/-- The complementary quotient in (15.3) on the literal original second endpoint. The normal
order-eighteen subgroup is the image of the proved reduced quotient inclusion;
no original quotient identification is assumed. -/
theorem original_second_quotient_marked_of_ne (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    ∃ d : (parabolic L S j ⧸ pCore 2 (parabolic L S j)) ≃* (S3 × S3),
      ∃ c : C3 →* S3, Function.Injective c ∧
        ∀ x, d (coreQuotientMap h j x) =
          ((reducedSecondQuotientEquiv j f x).1,c (reducedSecondQuotientEquiv j f x).2) := by
  let := h.finite_parabolic j
  let A := parabolic L S j ⧸ pCore 2 (parabolic L S j)
  have hc : Nat.card A = 36 := by
    have hh := (pCore 2 (parabolic L S j)).card_mul_index
    rw [original_second_core_card h j f,original_second_card_of_ne h i j e f hne,
      index_eq_card] at hh
    change 64 * Nat.card A = 2304 at hh
    omega
  have hq : pCore 2 A = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 (parabolic L S j))
    apply comap_injective (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    rw [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk,
      MonoidHom.comap_bot,QuotientGroup.ker_mk']
  let J := (coreQuotientMap h j).range
  let : J.Normal := quotientMap_range_normal h j
  let d := MonoidHom.ofInjective (coreQuotientMap_injective h j)
  obtain ⟨v,c,hc,hv⟩ := second_quotient_extension_marked hc hq J
    (d.symm.trans (reducedSecondQuotientEquiv j f))
  refine ⟨v,c,hc,fun x => ?_⟩
  have hh := hv (d x)
  simp only [MulEquiv.trans_apply,d.symm_apply_apply] at hh
  simpa only [d, MonoidHom.ofInjective_apply] using hh

/-- The original second core quotient is a product of two symmetric triples. -/
theorem original_second_quotient_of_ne (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    Nonempty ((parabolic L S j ⧸ pCore 2 (parabolic L S j)) ≃* (S3 × S3)) := by
  obtain ⟨d,_,_,_⟩ := original_second_quotient_marked_of_ne h i j e f hne
  exact ⟨d⟩

/-- The image of the original Sylow in the original second core quotient
is elementary abelian of order four. -/
theorem original_second_sylow_image (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    let R := (S.subgroupOf (parabolic L S j)).map
      (QuotientGroup.mk' (pCore 2 (parabolic L S j)))
    IsElementaryAbelian 2 R ∧ Nat.card R = 4 := by
  let := h.finite_parabolic j
  obtain ⟨T,hT⟩ := h.sylow_parabolic j
  have ht : (T : Subgroup (parabolic L S j)) = S.subgroupOf (parabolic L S j) := by
    apply map_injective (parabolic L S j).subtype_injective
    rw [hT,map_subgroupOf_eq_of_le (show S ≤ parabolic L S j from le_sup_right.trans le_sup_left)]
  obtain ⟨d⟩ := original_second_quotient_of_ne h i j e f hne
  have hh := SymmetricThreeProductResidual.sylow_elementary_four d
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (parabolic L S j))))
  change IsElementaryAbelian 2 ((T : Subgroup (parabolic L S j)).map (QuotientGroup.mk' (pCore 2 (parabolic L S j)))) ∧ Nat.card ((T : Subgroup (parabolic L S j)).map (QuotientGroup.mk' (pCore 2 (parabolic L S j)))) = 4 at hh
  rwa [ht] at hh

/-- Every square of an original Sylow element lies in the unchanged second
core. This is a quotient statement, not yet a lift to an outer involution. -/
theorem original_sylow_square_mem_second_core (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) (x : G) (hx : x ∈ S) :
    x ^ 2 ∈ twoCore (parabolic L S j) := by
  let P := parabolic L S j
  let q := QuotientGroup.mk' (pCore 2 P)
  let R := (S.subgroupOf P).map q
  let : IsElementaryAbelian 2 R := (original_second_sylow_image h i j e f hne).1
  let y : P := ⟨x,(le_sup_right.trans le_sup_left : S ≤ P) hx⟩
  have hy : q y ∈ R := mem_map_of_mem q hx
  have hs : q (y ^ 2) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := R) (q y) hy
  exact mem_map_of_mem P.subtype ((QuotientGroup.eq_one_iff _).mp hs)


/-- The full original Borel modulo its own two-core is S₃ in the proper
extension. Its odd factor is retained. -/
theorem original_borel_quotient_of_ne (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S ≠ reducedSylow L S) :
    Nonempty ((commonBorel L S ⧸ pCore 2 (commonBorel L S)) ≃* S3) := by
  let := h.finite_commonBorel
  let B := commonBorel L S
  let q := QuotientGroup.mk' (pCore 2 B)
  have hs : Nat.card (pCore 2 B) = 128 := by
    have hh := reduced_sylow_card h i e
    change Nat.card ((pCore 2 B).map B.subtype) = 128 at hh
    rwa [card_map_of_injective B.subtype_injective] at hh
  have hc : Nat.card (B ⧸ pCore 2 B) = 6 := by
    have hh := (pCore 2 B).card_mul_index
    rw [hs,original_borel_card_of_ne h i e b hne,index_eq_card] at hh
    omega
  have hq : pCore 2 (B ⧸ pCore 2 B) = ⊥ := by
    apply comap_injective (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    rw [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk,
      MonoidHom.comap_bot,QuotientGroup.ker_mk']
  exact symmetric_three_of_six hc hq

/-- Under any resulting S₃ coordinates, the whole reduced Borel is exactly
the inverse image of A₃. This retains its literal inclusion in B. -/
theorem original_borel_quotient_reduced (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (hne : S ≠ reducedSylow L S)
    (d : (commonBorel L S ⧸ pCore 2 (commonBorel L S)) ≃* S3)
    (x : commonBorel L S) :
    d (QuotientGroup.mk' (pCore 2 (commonBorel L S)) x) ∈ alternatingGroup (Fin 3) ↔
      (x : G) ∈ commonBorel L (reducedSylow L S) := by
  let := h.finite_commonBorel
  let B := commonBorel L S
  let N := (commonBorel L (reducedSylow L S)).subgroupOf B
  let := reduced_borel_normal h
  let q := QuotientGroup.mk' (pCore 2 B)
  let v := d.toMonoidHom.comp q
  have hv : Function.Surjective v := d.surjective.comp (QuotientGroup.mk'_surjective _)
  let J := N.map v
  let : J.Normal := (reduced_borel_normal h).map v hv
  have hk : v.ker ≤ N := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
    intro z hz
    exact (show reducedSylow L S ≤ commonBorel L (reducedSylow L S) from le_sup_right)
      (show (z : G) ∈ reducedSylow L S from mem_map_of_mem B.subtype hz)
  have hi : J.index = 2 := by
    rw [← J.index_comap_of_surjective hv,comap_map_eq,sup_eq_left.mpr hk]
    exact original_borel_index_two_of_ne h i e hne
  have hj : Nat.card J = 3 := by
    have hh := J.card_mul_index
    rw [hi,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hJA : J = alternatingGroup (Fin 3) := by
    have hle : J ≤ alternatingGroup (Fin 3) := by
      intro z hz
      have hz3 : z ^ 3 = 1 := by
        have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : J))
        rw [hj] at hh
        exact congrArg Subtype.val hh
      exact (show ∀ z : S3, z ^ 3 = 1 → z ∈ alternatingGroup (Fin 3) by
        simp only [Equiv.Perm.mem_alternatingGroup]
        decide +kernel) z hz3
    apply eq_of_le_of_card_ge hle
    rw [hj,nat_card_alternatingGroup,Nat.card_fin]
    decide
  change v x ∈ alternatingGroup (Fin 3) ↔ x ∈ N
  rw [← hJA]
  exact ⟨fun hx => (show J.comap v ≤ N by
    rw [comap_map_eq,sup_eq_left.mpr hk]) hx,mem_map_of_mem v⟩

/-- Every original Borel actor outside the reduced Borel inverts its odd
quotient. This does not assert that the actor itself is an involution. -/
theorem original_outer_inverts_reduced_borel_mod_core
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S ≠ reducedSylow L S)
    (x y : commonBorel L S)
    (hx : (x : G) ∉ commonBorel L (reducedSylow L S))
    (hy : (y : G) ∈ commonBorel L (reducedSylow L S)) :
    QuotientGroup.mk' (pCore 2 (commonBorel L S)) (x * y * x⁻¹) =
      QuotientGroup.mk' (pCore 2 (commonBorel L S)) y⁻¹ := by
  obtain ⟨d⟩ := original_borel_quotient_of_ne h i e b hne
  let q := QuotientGroup.mk' (pCore 2 (commonBorel L S))
  have hx' : d (q x) ∉ alternatingGroup (Fin 3) :=
    fun hh => hx ((original_borel_quotient_reduced h i e hne d x).mp hh)
  have hy' := (original_borel_quotient_reduced h i e hne d y).mpr hy
  apply d.injective
  simp only [map_mul,map_inv]
  exact (show ∀ a c : S3, a ∉ alternatingGroup (Fin 3) →
    c ∈ alternatingGroup (Fin 3) → a*c*a⁻¹ = c⁻¹ by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel) _ _ hx' hy'

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
