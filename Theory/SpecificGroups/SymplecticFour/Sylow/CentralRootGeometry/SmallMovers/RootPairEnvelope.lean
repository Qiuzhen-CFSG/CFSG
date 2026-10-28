module
public import Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair.Recognition
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairMarking
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Rank-one overgroups of a full root or root pair

The first hyperbolic-plane SL₂ commutes with the second long root.
Their literal matrix product embeds SL₂ times an optional additive field.
The first projection identifies the full two-core kernel, while its
Sylow preimage maps to exactly the prescribed root or orthogonal root pair.
Inner conjugation handles arbitrary two-root positions. Pulling this
overgroup back through a surjection with two-group kernel retains the
entire original kernel and the specified Sylow subgroup.

This proves clauses (i)--(ii) of the subgroup F construction in MS93
(5.1), printed p.913. The original replacement application is in
NonbinarySymplectic.CriticalReduction.RootProductGeometry. Noncentrality
on the Thompson central omega, the further Baumann-Sylow construction F₀,
and Niles pushing-up are not conclusions of this module.
-/

@[expose] public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 2) F

def optionalField (b : Bool) : Subgroup (Multiplicative F) := if b then ⊤ else ⊥

omit [CharP F 2] [Finite F] in
private theorem first_second_commute (A : SL) (z : F) :
    Commute (OppositeLongRootPair.embedding A) (rootElement 2 z) := by
  apply Subtype.ext
  change OppositeLongRootPair.matrix A * rootMatrix 2 z =
    rootMatrix 2 z * OppositeLongRootPair.matrix A
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [OppositeLongRootPair.matrix,rootMatrix,Matrix.fromBlocks,
      Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.single]

def embedding (b : Bool) : SL × optionalField (F := F) b →* Sp F where
  toFun x := OppositeLongRootPair.embedding x.1 * rootElement 2 x.2.val.toAdd
  map_one' := by simp [RootSubgroup.element_zero]
  map_mul' x y := by
    change OppositeLongRootPair.embedding (x.1*y.1) *
      rootElement 2 (x.2.val.toAdd+y.2.val.toAdd) = _
    rw [map_mul,←RootSubgroup.element_add]
    change (OppositeLongRootPair.embedding x.1 * OppositeLongRootPair.embedding y.1) *
      (rootElement 2 x.2.val.toAdd * rootElement 2 y.2.val.toAdd) =
        (OppositeLongRootPair.embedding x.1 * rootElement 2 x.2.val.toAdd) *
          (OppositeLongRootPair.embedding y.1 * rootElement 2 y.2.val.toAdd)
    exact (first_second_commute y.1 x.2.val.toAdd).mul_mul_mul_comm _ _

omit [CharP F 2] [Finite F] in
private theorem embedding_matrix (b : Bool) (x : SL × optionalField (F := F) b) :
    (embedding b x).val = Matrix.fromBlocks
      !![x.1 0 0,0;0,1] !![x.1 0 1,0;0,x.2.val.toAdd]
      !![x.1 1 0,0;0,0] !![x.1 1 1,0;0,1] := by
  change OppositeLongRootPair.matrix x.1 * rootMatrix 2 x.2.val.toAdd = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [OppositeLongRootPair.matrix,rootMatrix,Matrix.fromBlocks,
      Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.single]

omit [CharP F 2] [Finite F] in
theorem embedding_injective (b : Bool) : Function.Injective (embedding (F := F) b) := by
  intro x y he
  have hh := congrArg (fun g : Sp F => g.val) he
  rw [embedding_matrix,embedding_matrix] at hh
  have hA : x.1=y.1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun M => M (.inl 0) (.inl 0)) hh
    · exact congrArg (fun M => M (.inl 0) (.inr 0)) hh
    · exact congrArg (fun M => M (.inr 0) (.inl 0)) hh
    · exact congrArg (fun M => M (.inr 0) (.inr 0)) hh
  have hz : x.2=y.2 := by
    apply Subtype.ext
    exact congrArg Multiplicative.ofAdd (congrArg (fun M => M (.inl 1) (.inr 1)) hh)
  exact Prod.ext hA hz

def group (b : Bool) : Subgroup (Sp F) := (embedding (F := F) b).range

def sylowImage (b : Bool) : Subgroup (Sp F) :=
  rootImage none ⊔ if b then rootImage (some 0) else ⊥

omit [CharP F 2] [Finite F] in
private theorem root_zero (t : F) : (element 0 t 0 0).val = rootElement 0 t := by
  simp [element,RootSubgroup.element_zero]

omit [CharP F 2] [Finite F] in
private theorem root_second (t : F) : (element 0 0 0 t).val = rootElement 2 t := by
  simp [element,RootSubgroup.element_zero]

theorem first_root_mem_iff (g : Sp F) :
    g ∈ rootImage (none : Option F) ↔ ∃ t : F, rootElement 0 t = g := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    obtain ⟨rfl,rfl,rfl⟩ := (element_mem_root _ _ _ _).mp hx
    exact ⟨u,(root_zero u).symm⟩
  · rintro ⟨t,rfl⟩
    rw [←root_zero t]
    exact mem_map_of_mem _ ((element_mem_root _ _ _ _).mpr ⟨rfl,rfl,rfl⟩)

omit [Finite F] in
theorem second_root_mem_iff (g : Sp F) :
    g ∈ rootImage (some (0:F)) ↔ ∃ t : F, rootElement 2 t = g := by
  constructor
  · rintro ⟨x,⟨v,rfl⟩,rfl⟩
    refine ⟨v.toAdd,?_⟩
    change rootElement 2 v.toAdd = (element 0 (0^2*v.toAdd) (0*v.toAdd) v.toAdd).val
    simpa using (root_second v.toAdd).symm
  · rintro ⟨t,rfl⟩
    rw [←root_second t]
    exact mem_map_of_mem _ ((element_mem_finiteRoot _ _ _ _ _).mpr (by simp))

theorem fst_kernel_pgroup (b : Bool) :
    IsPGroup 2 (MonoidHom.fst SL (optionalField (F := F) b)).ker := by
  let f := MonoidHom.fst SL (optionalField (F := F) b)
  let r : f.ker →* optionalField (F := F) b := (MonoidHom.snd _ _).comp f.ker.subtype
  have hr : Function.Injective r := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (x.property.trans y.property.symm) h
  have hF : IsPGroup 2 (Multiplicative F) := by
    let := Fintype.ofFinite F
    obtain ⟨n,hn,hc⟩ := FiniteField.card F 2
    apply IsPGroup.of_card (n := n)
    simpa [Nat.card_eq_fintype_card] using hc
  exact (hF.to_subgroup (optionalField b)).of_injective r hr

def sylow (b : Bool) : Sylow 2 (SL × optionalField (F := F) b) :=
  (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2).comapOfKerIsPGroup
    (MonoidHom.fst _ _) (fst_kernel_pgroup (F := F) b) (by
      rw [MonoidHom.range_eq_top_of_surjective _ (fun x => ⟨(x,1),rfl⟩)]
      exact le_top)

theorem sylow_map (b : Bool) :
    (sylow (F := F) b : Subgroup (SL × optionalField b)).map (embedding b) = sylowImage b := by
  apply le_antisymm
  · rintro _ ⟨⟨A,z⟩,hA,rfl⟩
    obtain ⟨t,rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F A).mp hA
    change OppositeLongRootPair.embedding _ * rootElement 2 z.val.toAdd ∈ _
    rw [OppositeLongRootPair.embedding_upper]
    apply mul_mem (mem_sup_left ((first_root_mem_iff _).mpr ⟨t,rfl⟩))
    apply mem_sup_right
    cases b with
    | false =>
      have hz : z.val=1 := z.property
      simp [hz,RootSubgroup.element_zero]
    | true => exact (second_root_mem_iff _).mpr ⟨z.val.toAdd,rfl⟩
  · apply sup_le
    · intro g hg
      obtain ⟨t,rfl⟩ := (first_root_mem_iff g).mp hg
      refine ⟨((Matrix.SpecialLinearGroup.transvection zero_ne_one t : SL),
        (1 : optionalField (F := F) b)),?_,?_⟩
      · exact (Matrix.SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨t,rfl⟩
      · change OppositeLongRootPair.embedding (F := F) _ * rootElement 2 (0:F) = _
        rw [OppositeLongRootPair.embedding_upper,RootSubgroup.element_zero,mul_one]
    · cases b with
      | false => exact bot_le
      | true =>
        intro g hg
        obtain ⟨t,rfl⟩ := (second_root_mem_iff g).mp hg
        refine ⟨((1 : SL),(⟨Multiplicative.ofAdd t,mem_top _⟩ : optionalField (F := F) true)),?_,?_⟩
        · exact (Matrix.SpecialLinearGroup.upperUnipotent F).one_mem
        · change OppositeLongRootPair.embedding 1 * rootElement 2 t = _
          rw [map_one,one_mul]

/-- The rank-one envelope contains the prescribed full root Sylow and
has the literal SL₂ quotient by its whole two-core. -/
theorem exists_envelope (b : Bool) :
    ∃ S : Sylow 2 (group (F := F) b),
      (S : Subgroup (group (F := F) b)).map (group (F := F) b).subtype = sylowImage b ∧
      Nonempty ((group (F := F) b ⧸ pCore 2 (group (F := F) b)) ≃* SL) := by
  let e : SL × optionalField (F := F) b ≃* group (F := F) b :=
    MonoidHom.ofInjective (embedding_injective (F := F) b)
  let S : Sylow 2 (group (F := F) b) := (sylow (F := F) b).mapSurjective e.surjective
  have hs : (S : Subgroup (group (F := F) b)).map (group (F := F) b).subtype = sylowImage b := by
    change ((sylow (F := F) b : Subgroup (SL × optionalField b)).map e.toMonoidHom).map (group (F := F) b).subtype = _
    rw [Subgroup.map_map]
    exact sylow_map b
  let f := (MonoidHom.fst SL (optionalField b)).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (show Function.Surjective (MonoidHom.fst SL (optionalField b)) from
    fun A => ⟨(A,1),rfl⟩).comp e.symm.surjective
  have hk : IsPGroup 2 f.ker := (fst_kernel_pgroup (F := F) b).comap_of_injective
    e.symm.toMonoidHom e.symm.injective
  have hker : f.ker = pCore 2 (group (F := F) b) := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hk
    rw [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot] at hh
    exact hh
  exact ⟨S,hs,⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩⟩

/-- The marked Sylow lifts through the full original two-kernel. -/
theorem exists_preimage_envelope
    {G : Type*} [Group G] [Finite G]
    (f : G →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (J : Subgroup G) (hkJ : f.ker ≤ J) (b : Bool) (hJ : J.map f = sylowImage b) :
    ∃ I : Subgroup G, J ≤ I ∧
      ∃ S : Sylow 2 I, (S : Subgroup I).map I.subtype = J ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* SL) := by
  obtain ⟨P,hP,⟨eP⟩⟩ := exists_envelope (F := F) b
  let I := (group (F := F) b).comap f
  let q : I →* group (F := F) b := (f.comp I.subtype).codRestrict (group (F := F) b) (fun x => x.property)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,hy⟩ := hf x.val
    exact ⟨⟨y,by change f y ∈ group (F := F) b; rw [hy]; exact x.property⟩,Subtype.ext hy⟩
  have hqk : IsPGroup 2 q.ker := by
    have he : q.ker = f.ker.comap I.subtype := by
      ext x
      change q x=1 ↔ f x.val=1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  have hJI : J ≤ I := by
    intro x hx
    change f x ∈ group (F := F) b
    exact (hP ▸ map_subtype_le (P : Subgroup (group (F := F) b))) (hJ ▸ mem_map_of_mem f hx)
  let S := P.comapOfKerIsPGroup q hqk (by
    rw [MonoidHom.range_eq_top_of_surjective q hq]; exact le_top)
  have hs : (S : Subgroup I) = J.subgroupOf I := by
    ext x
    change q x ∈ (P : Subgroup (group (F := F) b)) ↔ x.val ∈ J
    have hx : q x ∈ (P : Subgroup (group (F := F) b)) ↔ f x.val ∈ sylowImage b := by
      rw [←hP]
      exact (mem_map_iff_mem (group (F := F) b).subtype_injective).symm
    rw [hx,←hJ]
    change x.val ∈ (J.map f).comap f ↔ _
    rw [comap_map_eq_self hkJ]
  refine ⟨I,hJI,S,?_,⟨(q.pCoreQuotientEquiv hq hqk).trans eP⟩⟩
  rw [hs,map_subgroupOf_eq_of_le hJI]

/-- A pair of full roots supplies an actual rank-one overgroup with exactly
that Sylow image, without dropping the original kernel. -/
theorem exists_root_pair_preimage_envelope
    {G : Type*} [Group G] [Finite G]
    (f : G →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (J : Subgroup G) (hkJ : f.ker ≤ J) (s t : Option F)
    (hJ : J.map f = rootImage s ⊔ rootImage t) :
    ∃ I : Subgroup G, J ≤ I ∧
      ∃ S : Sylow 2 I, (S : Subgroup I).map I.subtype = J ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* SL) := by
  obtain ⟨g,hg⟩ := rootPair_standard_first s t
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x)=1 ↔ f x=1
    exact (MulAut.conj g).map_eq_one_iff
  have hm : J.map f' = (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom := by
    rw [←Subgroup.map_map,hJ]
  rcases hg with hg | hg
  · exact exists_preimage_envelope f' hf' (hker ▸ hk) J (hker ▸ hkJ) false
      (by simpa only [sylowImage,Bool.false_eq_true,↓reduceIte,sup_bot_eq] using hm.trans hg)
  · exact exists_preimage_envelope f' hf' (hker ▸ hk) J (hker ▸ hkJ) true
      (by simpa only [sylowImage,↓reduceIte] using hm.trans hg)

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
