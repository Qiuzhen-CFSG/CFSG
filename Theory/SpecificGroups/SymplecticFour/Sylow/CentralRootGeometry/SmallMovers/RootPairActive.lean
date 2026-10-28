module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairPlacement

/-!
# Choosing the active root in a rank-one envelope

An explicit symplectic permutation exchanges the two standard long roots.
A nontrivial subgroup of their join can therefore be placed outside the
inactive root. The whole two-core of the rank-one envelope lies in that
inactive root, so lifting through a full two-kernel keeps the prescribed
escaping subgroup outside the envelope's two-core. The same envelope
retains the full Sylow, residual movement and marked point parabolic.

Source: the choice of F in MS93 (5.1), printed p.913. The actual replacement
application is CriticalReduction.RootProductActive; the further Baumann
Sylow equality is not asserted here.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix Representation
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def swapPairs : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1

omit [Finite F] in
private theorem swapPairs_matrix : (swapPairs (F := F)).val =
    fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0] := by
  change rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem swap_roots (t : F) :
    swapPairs * rootElement 0 t * swapPairs⁻¹ = rootElement 2 t ∧
    swapPairs * rootElement 2 t * swapPairs⁻¹ = rootElement 0 t := by
  have h (r r' : Fin 8)
      (he : (swapPairs (F := F)).val * rootMatrix r t =
        rootMatrix r' t * (swapPairs (F := F)).val) :
      swapPairs * rootElement r t * swapPairs⁻¹ = rootElement r' t := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext he
  constructor <;> apply h <;> rw [swapPairs_matrix] <;>
    ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks]

private theorem swap_root_images :
    (rootImage (none : Option F)).map (MulAut.conj swapPairs).toMonoidHom = rootImage (some 0) ∧
    (rootImage (some (0:F))).map (MulAut.conj swapPairs).toMonoidHom = rootImage none := by
  have h (A B : Subgroup (Sp F)) (hc : Nat.card A = Nat.card B)
      (hl : A.map (MulAut.conj swapPairs).toMonoidHom ≤ B) :
      A.map (MulAut.conj swapPairs).toMonoidHom = B :=
    eq_of_le_of_card_ge hl (by rw [card_map_of_injective (MulAut.conj swapPairs).injective,hc])
  constructor
  · apply h
    · simp only [rootImage,card_map_of_injective (unipotent (F := F)).subtype_injective,card_rootFamily]
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨t,rfl⟩ := (first_root_mem_iff x).mp hx
      change swapPairs * rootElement 0 t * swapPairs⁻¹ ∈ _
      rw [(swap_roots t).1]
      exact (second_root_mem_iff _).mpr ⟨t,rfl⟩
  · apply h
    · simp only [rootImage,card_map_of_injective (unipotent (F := F)).subtype_injective,card_rootFamily]
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨t,rfl⟩ := (second_root_mem_iff x).mp hx
      change swapPairs * rootElement 2 t * swapPairs⁻¹ ∈ _
      rw [(swap_roots t).2]
      exact (first_root_mem_iff _).mpr ⟨t,rfl⟩

private theorem standard_roots_inf :
    rootImage (none : Option F) ⊓ rootImage (some (0:F)) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨s,hs⟩ := (first_root_mem_iff x).mp hx.1
  obtain ⟨t,ht⟩ := (second_root_mem_iff x).mp hx.2
  have hh := congrArg (fun x : Sp F => x.val (.inl 0) (.inr 0)) (hs.trans ht.symm)
  have hs0 : s=0 := by simpa [rootElement,rootMatrix,fromBlocks,Matrix.single] using hh
  rw [←hs,hs0,RootSubgroup.element_zero]
  exact one_mem _

/-- An escaping subgroup of a root pair can be kept outside the inactive root.
The conjugation fixes the full root-pair Sylow in standard position. -/
theorem active_root_pair_coordinates (s t : Option F) (A : Subgroup (Sp F))
    (hA : A ≤ rootImage s ⊔ rootImage t) (hne : A ≠ ⊥) :
    ∃ g : Sp F, ∃ b : Bool,
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom = sylowImage b ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ rootImage (some 0) := by
  obtain ⟨g,hg | hg⟩ := rootPair_standard_first s t
  · refine ⟨g,false,by simpa [sylowImage] using hg,?_⟩
    intro ha
    have hh : A.map (MulAut.conj g).toMonoidHom ≤ ⊥ := by
      rw [←standard_roots_inf]
      exact le_inf ((map_mono hA).trans_eq hg) ha
    exact hne ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp (bot_unique hh))
  · by_cases ha : A.map (MulAut.conj g).toMonoidHom ≤ rootImage (some 0)
    · have hm (B : Subgroup (Sp F)) :
          B.map (MulAut.conj (swapPairs*g)).toMonoidHom =
            (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj swapPairs).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply,mul_assoc]
      refine ⟨swapPairs*g,true,?_,?_⟩
      · rw [hm,hg,Subgroup.map_sup,swap_root_images.1,swap_root_images.2]
        simp [sylowImage,sup_comm]
      · intro hb
        have hh : A.map (MulAut.conj (swapPairs*g)).toMonoidHom ≤ ⊥ := by
          rw [←standard_roots_inf]
          refine le_inf ?_ hb
          rw [hm]
          exact (map_mono ha).trans_eq swap_root_images.2
        exact hne ((map_eq_bot_iff_of_injective _ (MulAut.conj (swapPairs*g)).injective).mp
          (bot_unique hh))
    · exact ⟨g,true,by simpa [sylowImage] using hg,ha⟩

/-- The whole two-core of the model envelope is contained in the inactive root. -/
theorem group_pCore_image_le_second_root (b : Bool) :
    (pCore 2 (group (F := F) b)).map (group (F := F) b).subtype ≤ rootImage (some 0) := by
  let e : Matrix.SpecialLinearGroup (Fin 2) F × optionalField (F := F) b ≃* group (F := F) b :=
    MonoidHom.ofInjective (embedding_injective (F := F) b)
  let f := (MonoidHom.fst (Matrix.SpecialLinearGroup (Fin 2) F) (optionalField b)).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (show Function.Surjective (MonoidHom.fst
      (Matrix.SpecialLinearGroup (Fin 2) F) (optionalField (F := F) b)) from
    fun x => ⟨(x,1),rfl⟩).comp e.symm.surjective
  have hk : IsPGroup 2 f.ker := (fst_kernel_pgroup (F := F) b).comap_of_injective
    e.symm.toMonoidHom e.symm.injective
  have he : f.ker = pCore 2 (group (F := F) b) := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hk
    rwa [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot] at hh
  rintro _ ⟨x,hx,rfl⟩
  have hx1 : (e.symm x).1=1 := by
    change x ∈ f.ker
    rwa [he]
  have hv : (x : Sp F) = rootElement 2 (e.symm x).2.val.toAdd := by
    have hh := congrArg (fun y : group (F := F) b => (y : Sp F)) (e.apply_symm_apply x)
    change embedding b (e.symm x) = (x : Sp F) at hh
    rw [←hh]
    change OppositeLongRootPair.embedding (e.symm x).1 * rootElement 2 _ = _
    rw [hx1,map_one,one_mul]
  change (x : Sp F) ∈ rootImage (some 0)
  rw [hv]
  exact (second_root_mem_iff _).mpr ⟨_,rfl⟩

variable [Algebra (ZMod 2) F]
open Representation.BinaryOffender
local notation "τ" => restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)

/-- The active root choice keeps the prescribed escaping subgroup outside
O₂ of the rank-one envelope, with the same full Sylow and natural action. -/
theorem exists_active_moving_root_pair_envelope
    {G : Type*} [Group G] [Finite G]
    (f : G →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (U J A : Subgroup G) (hkJ : f.ker ≤ J) (hAJ : A ≤ J) (hAk : ¬ A ≤ f.ker)
    (s t : Option F) (hJ : J.map f = rootImage s ⊔ rootImage t)
    (hindex : ∀ B : Subgroup G, (centralizer (B : Set G)).relIndex U =
      2 ^ fixedCodim τ (B.map f)) :
    ∃ I : Subgroup G, J ≤ I ∧
      ∃ S : Sylow 2 I, (S : Subgroup I).map I.subtype = J ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
        ⁅U ⊓ centralizer (J : Set G), (pResidual 2 I).map I.subtype⁆ ≠ ⊥ ∧
        ¬ A ≤ (pCore 2 I).map I.subtype ∧
        ∃ g : Sp F, I.map ((MulAut.conj g).toMonoidHom.comp f) ≤
          Theory.SpecificGroups.SymplecticFour.stabilizer (F ∙ e (F := F) 1) := by
  have hne : A.map f ≠ ⊥ := by
    intro hz
    exact hAk (((map_eq_bot_iff A).mp hz))
  obtain ⟨g,b,hg,hactive⟩ := active_root_pair_coordinates s t (A.map f)
    ((map_mono hAJ).trans_eq hJ) hne
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x)=1 ↔ f x=1
    exact (MulAut.conj g).map_eq_one_iff
  have hm : J.map f' = sylowImage b := by rw [←Subgroup.map_map,hJ,hg]
  have hi : ∀ B : Subgroup G, (centralizer (B : Set G)).relIndex U =
      2 ^ fixedCodim τ (B.map f') := by
    intro B
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hindex B
  obtain ⟨I,hJI,hIm,S,hS,he,hn⟩ := exists_moving_preimage_envelope
    f' hf' (hker ▸ hk) U J (hker ▸ hkJ) b hm hi
  let q : I →* group (F := F) b := (f'.comp I.subtype).codRestrict (group b)
    (fun x => hIm ▸ mem_map_of_mem f' x.property)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,hy,he⟩ := (show x.val ∈ I.map f' from hIm.symm ▸ x.property)
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  have hcore : (pCore 2 I).map q ≤ pCore 2 (group (F := F) b) :=
    le_sSup ⟨Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
  have hcore' : ((pCore 2 I).map I.subtype).map f' ≤ rootImage (some 0) := by
    have hh := (map_mono (f := (group (F := F) b).subtype) hcore).trans
      (group_pCore_image_le_second_root b)
    have hcomp : (group (F := F) b).subtype.comp q = f'.comp I.subtype := by
      ext x
      rfl
    simpa only [Subgroup.map_map,hcomp] using hh
  refine ⟨I,hJI,S,hS,he,hn,?_,g,hIm.le.trans (group_le_second_point_stabilizer b)⟩
  intro hbad
  apply hactive
  rw [Subgroup.map_map]
  exact (map_mono hbad).trans hcore'

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
