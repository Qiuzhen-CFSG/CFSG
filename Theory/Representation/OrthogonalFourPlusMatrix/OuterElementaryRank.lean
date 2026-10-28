module

public import Theory.Representation.OrthogonalFourPlusMatrix.ElementaryNormalizerGeometry

/-!
# Large elementary actors in the binary determinant normalizer

Every elementary subgroup of order at least sixteen in the full binary
linear normalizer of SL₂(4) × SL₂(4) lies in the original determinant image.
Its faithful conjugation action embeds it in Aut(A₅ × A₅). The maximum-rank
wreath calculation splits that image into its two independent projections.
An additive involution centralizing one whole SL₂ factor is multiplication
by a matrix from the other factor: its square makes the determinant one.
Lifting the two projections therefore puts the original actor in the image.

The final theorem transports this containment to any faithful action with
that marked normal subgroup, preserving the original actor and embedding.
It supplies the outer-actor rank bound used to exclude G.11.2(7) in
Aschbacher--Smith 14.3.14, printed p.994 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Matrix Module Subgroup Theory.GroupTheory
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation.BinaryOffender
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective
private def columnInsert (j : Fin 2) (v : Fin 2 → F) : Mat (F := F) :=
  fun i k => if k = j then v i else 0

private lemma columnInsert_left (A : Mat (F := F)) (j : Fin 2) (v : Fin 2 → F) :
    A * columnInsert j v = columnInsert j (A.mulVec v) := by
  funext i k
  fin_cases k <;> fin_cases j <;>
    simp [columnInsert, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem left_centralizer (f : V →+ V)
    (hleft : ∀ (A : SpecialLinearGroup (Fin 2) F) (M : V),
      f (A.val * M) = A.val * f M) :
    ∃ C : V, ∀ M, f M = M * C := by
  have hblock (j k : Fin 2) : ∃ c : F, ∀ v : Fin 2 → F,
      (fun i => f (columnInsert k v) i j) = c • v := by
    let b : (Fin 2 → F) →+ (Fin 2 → F) :=
      { toFun := fun v i => f (columnInsert k v) i j
        map_zero' := by
          have he : columnInsert k (0 : Fin 2 → F) = 0 := by funext i l; simp [columnInsert]
          change (fun i => f (columnInsert k 0) i j) = 0
          rw [he, f.map_zero]
          rfl
        map_add' := by
          intro v w
          have he : columnInsert k (v + w) = columnInsert k v + columnInsert k w := by
            funext i l
            by_cases h : l = k <;> simp [columnInsert, h]
          change (fun i => f (columnInsert k (v + w)) i j) = _
          rw [he, f.map_add]
          rfl }
    apply Representation.SL2NaturalOffenders.centralizer_scalar b
    intro A v
    change (fun i => f (columnInsert k (A.val.mulVec v)) i j) = _
    rw [← columnInsert_left, hleft]
    rfl
  choose c hc using hblock
  have hformula (M : Mat (F := F)) (i j : Fin 2) :
      f M i j = c j 0 * M i 0 + c j 1 * M i 1 := by
    have he : M = columnInsert 0 (fun i => M i 0) + columnInsert 1 (fun i => M i 1) := by
      funext i j
      fin_cases j <;> simp [columnInsert]
    have h0 := congrFun (hc j 0 (fun i => M i 0)) i
    have h1 := congrFun (hc j 1 (fun i => M i 1)) i
    conv_lhs => rw [he, map_add]
    exact congrArg₂ (· + ·) h0 h1
  let C : Mat (F := F) := fun i j => c j i
  have hformula' (M : Mat (F := F)) : f M = M * C := by
    funext i j
    rw [hformula]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp only [C]
    ring
  exact ⟨C,hformula'⟩

private theorem sl_one : (1 : SpecialLinearGroup (Fin 2) F).val = 1 := rfl

private theorem left_centralizing_involution (t : V ≃ₗ[ZMod 2] V)
    (ht : ∀ M, t (t M) = M)
    (hc : ∀ (a : SpecialLinearGroup (Fin 2) F) M,
      t (action (a,1) M) = action (a,1) (t M)) :
    ∃ b : SpecialLinearGroup (Fin 2) F, ∀ M, t M = action (1,b) M := by
  obtain ⟨C,hC⟩ := left_centralizer (show V →+ V from
    { toFun := t, map_zero' := t.map_zero, map_add' := t.map_add }) (by
    intro a M
    have hh := hc a M
    change t (a.val * M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val) =
      a.val * t M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val at hh
    simpa [sl_one] using hh)
  change ∀ M, t M = M*C at hC
  have hC2 : C*C=1 := by simpa only [hC, one_mul] using ht 1
  have hd : C.det = 1 := by
    have hh := congrArg Matrix.det hC2
    rw [Matrix.det_mul, Matrix.det_one] at hh
    exact CharTwo.sq_injective (by simpa only [pow_two,one_mul] using hh)
  let b : SpecialLinearGroup (Fin 2) F := ⟨C,hd⟩
  have hb : b⁻¹=b := inv_eq_of_mul_eq_one_left (Subtype.ext hC2)
  refine ⟨b,fun M => ?_⟩
  change t M = (1 : SpecialLinearGroup (Fin 2) F).val * M * b⁻¹.val
  rw [hb,sl_one,one_mul]
  exact hC M

private theorem right_centralizing_involution (t : V ≃ₗ[ZMod 2] V)
    (ht : ∀ M, t (t M) = M)
    (hc : ∀ (a : SpecialLinearGroup (Fin 2) F) M,
      t (action (1,a) M) = action (1,a) (t M)) :
    ∃ b : SpecialLinearGroup (Fin 2) F, ∀ M, t M = action (b,1) M := by
  let τ := (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) F F).restrictScalars (ZMod 2)
  let s := τ.trans (t.trans τ)
  have hs : ∀ M, s (s M) = M := by
    intro M
    change (t ((t M.transpose).transpose.transpose)).transpose=M
    rw [Matrix.transpose_transpose,ht,Matrix.transpose_transpose]
  have hsc : ∀ (a : SpecialLinearGroup (Fin 2) F) M,
      s (action (a,1) M) = action (a,1) (s M) := by
    intro a M
    have hh := hc (a.transpose⁻¹) M.transpose
    change t ((1 : SpecialLinearGroup (Fin 2) F).val * M.transpose *
      (a.transpose⁻¹)⁻¹.val) = (1 : SpecialLinearGroup (Fin 2) F).val *
      t M.transpose * (a.transpose⁻¹)⁻¹.val at hh
    simp only [sl_one, one_mul, inv_inv,
      SpecialLinearGroup.coe_transpose] at hh
    change (t ((a.val*M*(1 : SpecialLinearGroup (Fin 2) F)⁻¹.val).transpose)).transpose =
      a.val*(t M.transpose).transpose*(1 : SpecialLinearGroup (Fin 2) F)⁻¹.val
    simpa only [inv_one,sl_one,mul_one,Matrix.transpose_mul,
      Matrix.transpose_transpose] using congrArg Matrix.transpose hh
  obtain ⟨b,hb⟩ := left_centralizing_involution s hs hsc
  refine ⟨b⁻¹.transpose,fun M => ?_⟩
  have hh := hb M.transpose
  change (t M).transpose = (1 : SpecialLinearGroup (Fin 2) F).val * M.transpose * b⁻¹.val at hh
  change t M = (b⁻¹.transpose).val * M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val
  simpa only [sl_one,one_mul,inv_one,mul_one,Matrix.transpose_mul,
    Matrix.transpose_transpose,SpecialLinearGroup.coe_transpose] using congrArg Matrix.transpose hh
open WreathTwoElementaryRank
open Theory.SpecificGroups.SymmetricFive.WreathElementaryRank (large_elementary_le_base)

private theorem maximum_wreath_splits
    (E : Subgroup Wreath) [IsElementaryAbelian 2 E] (hc : 16 ≤ Nat.card E)
    (w : E) :
    ∃ a b : Sym, baseHom (a,1) ∈ E ∧ baseHom (1,b) ∈ E ∧
      (w : Wreath) = baseHom (a,1) * baseHom (1,b) := by
  have hbase := large_elementary_le_base E inferInstance (lt_of_lt_of_le (by decide : 8 < 16) hc)
  let P := E.comap (baseHom : Sym × Sym →* Wreath)
  have hm : P.map baseHom = E := by
    apply map_comap_eq_self
    intro w hw
    exact ⟨baseEquiv.symm ⟨w,hbase hw⟩, (baseEquiv_coe _).symm.trans (congrArg Subtype.val
      (baseEquiv.apply_symm_apply ⟨w,hbase hw⟩))⟩
  have hPc : Nat.card P = Nat.card E := by
    rw [←hm,card_map_of_injective baseHom_injective]
  let : IsElementaryAbelian 2 P := by
    let f : P →* E := baseHom.restrict (fun _ hx => hx)
    exact IsElementaryAbelian.of_injective f (fun x y h =>
      Subtype.ext (baseHom_injective (congrArg Subtype.val h)))
  let A := P.map (MonoidHom.fst Sym Sym)
  let B := P.map (MonoidHom.snd Sym Sym)
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have ha : Nat.card A ≤ 4 := (primeRank_le_iff_elementary_card_le Sym).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two A hA
  have hb : Nat.card B ≤ 4 := (primeRank_le_iff_elementary_card_le Sym).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two B hB
  have hP : P ≤ A.prod B := by
    intro x hx
    exact ⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩
  have hprod : Nat.card (A.prod B) = Nat.card A * Nat.card B := by
    rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]
  have hle := card_le_of_le hP
  have hac : Nat.card A = 4 := by nlinarith
  have hbc : Nat.card B = 4 := by nlinarith
  have heq : P = A.prod B := eq_of_le_of_card_ge hP (by rw [hprod,hac,hbc]; omega)
  have hw : (w : Wreath) ∈ P.map baseHom := hm.symm ▸ w.property
  obtain ⟨⟨a,b⟩,hab,hw⟩ := hw
  have hab' : (a,b) ∈ A.prod B := heq ▸ hab
  refine ⟨a,b,show (a,1) ∈ P from heq.symm ▸ ⟨hab'.1,B.one_mem⟩,
    show (1,b) ∈ P from heq.symm ▸ ⟨A.one_mem,hab'.2⟩,?_⟩
  rw [←map_mul]
  simpa using hw.symm

private theorem wreath_left_fixed (a : Sym) (b : Alt) :
    wreathHom (baseHom (a,1)) (1,b)=(1,b) := by
  change wreathMap (baseHom (a,1)) (1,b)=(1,b)
  rw [wreathMap_apply]
  simp [baseHom,turn_ne_one]

private theorem wreath_right_fixed (b : Sym) (a : Alt) :
    wreathHom (baseHom (1,b)) (a,1)=(a,1) := by
  change wreathMap (baseHom (1,b)) (a,1)=(a,1)
  rw [wreathMap_apply]
  simp [baseHom,turn_ne_one]

private theorem supported_left_mem_actionImage
    (t : linearNormalizer action) (htwo : t ^ 2 = 1)
    (a : Sym) (hconj : alternatingConjugation t = wreathHom (baseHom (a,1))) :
    t.val ∈ actionImage action := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (t : linearNormalizer action).val
  have ht : ∀ M, e (e M)=M := by
    intro M
    have hh := htwo
    exact congrArg (fun x : linearNormalizer action => x.val.val M) hh
  have hfix (b : SpecialLinearGroup (Fin 2) F) :
      normalizerConjugation t (1,b)=(1,b) := by
    apply alternatingPairEquiv.injective
    have hh := MulEquiv.congr_fun hconj (alternatingPairEquiv (1,b))
    simp only [alternatingConjugation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hh
    have hp : alternatingPairEquiv (1,b) = (1,Representation.SL2FourNatural.alternatingFiveEquiv b) := by
      exact Prod.ext (Representation.SL2FourNatural.alternatingFiveEquiv.map_one) rfl
    rw [hp] at hh
    exact hh.trans (wreath_left_fixed a _ ) |>.trans hp.symm
  obtain ⟨b,hb⟩ := right_centralizing_involution e ht (by
    intro b M
    have hh := normalizerConjugation_action t (1,b) M
    rw [hfix] at hh
    exact hh.symm)
  exact ⟨(b,1),Units.ext (LinearMap.ext hb).symm⟩

private theorem supported_right_mem_actionImage
    (t : linearNormalizer action) (htwo : t ^ 2 = 1)
    (b : Sym) (hconj : alternatingConjugation t = wreathHom (baseHom (1,b))) :
    t.val ∈ actionImage action := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (t : linearNormalizer action).val
  have ht : ∀ M, e (e M)=M := by
    intro M
    have hh := htwo
    exact congrArg (fun x : linearNormalizer action => x.val.val M) hh
  have hfix (a : SpecialLinearGroup (Fin 2) F) :
      normalizerConjugation t (a,1)=(a,1) := by
    apply alternatingPairEquiv.injective
    have hh := MulEquiv.congr_fun hconj (alternatingPairEquiv (a,1))
    simp only [alternatingConjugation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hh
    have hp : alternatingPairEquiv (a,1) = (Representation.SL2FourNatural.alternatingFiveEquiv a,1) := by
      exact Prod.ext rfl (Representation.SL2FourNatural.alternatingFiveEquiv.map_one)
    rw [hp] at hh
    exact hh.trans (wreath_right_fixed b _) |>.trans hp.symm
  obtain ⟨a,ha⟩ := left_centralizing_involution e ht (by
    intro a M
    have hh := normalizerConjugation_action t (a,1) M
    rw [hfix] at hh
    exact hh.symm)
  exact ⟨(1,a),Units.ext (LinearMap.ext ha).symm⟩

/-- An elementary subgroup of rank four in the full binary normalizer
lies in the original determinant group. -/
theorem large_elementary_le_actionImage
    (A : Subgroup (linearNormalizer action)) [IsElementaryAbelian 2 A]
    (hc : 16 ≤ Nat.card A) : A.map (linearNormalizer action).subtype ≤ actionImage action := by
  let f : A →* Wreath := wreathEquiv.symm.toMonoidHom.comp
    (alternatingConjugation.comp A.subtype)
  have hf : Function.Injective f := wreathEquiv.symm.injective.comp
    (alternatingConjugation_elementary_injective A)
  let E := f.range
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hec : 16 ≤ Nat.card E := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact hc
  have hconj (t : A) : alternatingConjugation t = wreathHom (f t) := by
    change alternatingConjugation t = wreathHom (wreathEquiv.symm (alternatingConjugation t))
    rw [← wreathEquiv_apply, wreathEquiv.apply_symm_apply]
  rintro _ ⟨t,ht,rfl⟩
  let tA : A := ⟨t,ht⟩
  obtain ⟨a,b,ha,hb,he⟩ := maximum_wreath_splits E hec (f.rangeRestrict tA)
  obtain ⟨u,hu⟩ := ha
  obtain ⟨w,hw⟩ := hb
  have htuw : tA=u*w := hf (by rw [map_mul,hu,hw]; exact he)
  have htval : t.val=(u : linearNormalizer action).val*(w : linearNormalizer action).val :=
    congrArg (fun x : A => x.val.val) htuw
  change t.val ∈ actionImage action
  rw [htval]
  exact (actionImage action).mul_mem (supported_left_mem_actionImage u
    (elemPow_eq_one_of_isElementaryAbelian (u : linearNormalizer action) u.property) a
    ((hconj u).trans (congrArg wreathHom hu)))
    (supported_right_mem_actionImage w
      (elemPow_eq_one_of_isElementaryAbelian (w : linearNormalizer action) w.property) b
      ((hconj w).trans (congrArg wreathHom hw)))

end ClassicalOrthogonal.FourPlusMatrix.Binary
namespace Representation.BinaryOffender
open ClassicalOrthogonal.FourPlusMatrix.Binary

/-- A large elementary actor lies in a normal subgroup with the actual
binary determinant action. The original actor and the subgroup are retained. -/
theorem elementary_le_marked_determinant_of_card_ge_sixteen
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (hρ : Function.Injective ρ)
    (H : Subgroup D) [H.Normal] (e : H ≃* ClassicalOrthogonal.FourPlusMatrix.Binary.G)
    (E : U ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Binary.V)
    (he : ∀ (h : H) w, E (ρ h w) = action (e h) (E w))
    (X : Subgroup D) [IsElementaryAbelian 2 X] (hc : 16 ≤ Nat.card X) : X ≤ H := by
  let γ : Representation (ZMod 2) D V := E.conjRingEquiv.toMonoidHom.comp ρ
  have hE (g : D) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (h : H) : γ h = action (e h) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← hE]
    exact he h v
  have himage : H.map γ.asGroupHom = actionImage action := by
    ext z
    constructor
    · rintro ⟨h,hh,rfl⟩
      exact ⟨e ⟨h,hh⟩,Units.ext (hres ⟨h,hh⟩).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨h,rfl⟩ := e.surjective p
      exact ⟨h,h.property,Units.ext (hres h)⟩
  have hn (g : D) : γ.asGroupHom g ∈ linearNormalizer action := by
    change γ.asGroupHom g ∈ normalizer (actionImage action : Set _)
    rw [← himage]
    exact H.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (H : Set D) from
        le_normalizer_of_normal (mem_top g)))
  let j : D →* linearNormalizer action := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer action => z.val.val) hxy)
  let A := X.map j
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map j
  have hca : 16 ≤ Nat.card A := by rwa [Subgroup.card_map_of_injective hj]
  have hle := large_elementary_le_actionImage A hca
  intro x hx
  have hm : γ.asGroupHom x ∈ H.map γ.asGroupHom := by
    rw [himage]
    exact hle (mem_map_of_mem (linearNormalizer action).subtype (mem_map_of_mem j hx))
  obtain ⟨y,hy,heq⟩ := hm
  have hyx : y=x := hγ (congrArg Units.val heq)
  exact hyx ▸ hy
end Representation.BinaryOffender
