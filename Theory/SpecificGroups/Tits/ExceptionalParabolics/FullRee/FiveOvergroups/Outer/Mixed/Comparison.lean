module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Semilinear
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.ExtensionCore
public import Theory.GroupTheory.IndexTwoExtensionEquivalence

/-! The literal full-Ree max4 normalizer is the genuine mixed semilinear
PSL₂(25)⁺ extension. The native core marking intertwines both generator
actions and the outside square. The index-two normal-form theorem then
constructs the equivalence and retains both its core and outside values.
Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

@[expose] public section
open Subgroup
noncomputable section
namespace Tits.Max4Outer.Mixed
open Max4Projective GorensteinWalter MinimumIndexCandidates ExceptionalParabolics.FullRee
open ExceptionalParabolics.FullRee.FiveOvergroups

theorem native_basis (i : Fin 2) : nativeEquiv (coreBasis i)=pi (slGen i) := by
  fin_cases i
  · exact nativeEquiv_first
  · exact nativeEquiv_second

theorem native_word (w : List (Fin 2 × Bool)) : nativeEquiv (eval coreBasis w)=pi (slWord w) := by
  calc
    nativeEquiv (eval coreBasis w)=eval (fun i=>nativeEquiv (coreBasis i)) w :=
      map_eval nativeEquiv.toMonoidHom coreBasis w
    _=eval (fun i=>pi (slGen i)) w := by simp only [native_basis]
    _=pi (eval slGen w) := (map_eval pi slGen w).symm
    _=pi (slWord w) := by rw [slWord_eq]

theorem eval_invRev {ι G : Type*} [Group G] (f : ι → G) (w : List (ι × Bool)) :
    eval f (FreeGroup.invRev w)=(eval f w)⁻¹ := by
  rw [← lift_word f (FreeGroup.invRev w),← lift_word f w]
  exact (FreeGroup.lift f).map_inv (FreeGroup.mk w)

theorem native_square : nativeEquiv ⟨squareElement,square_mem⟩=pi (slWord inverseSquareWord) := by
  have hh : (⟨squareElement,square_mem⟩ : max4)=(eval coreBasis squareWord)⁻¹ := by
    apply Subtype.ext
    change squareElement=((eval coreBasis squareWord).val)⁻¹
    rw [eval_basis_val]
    rfl
  rw [hh,map_inv,native_word,slWord_eq,slWord_eq,inverseSquareWord,eval_invRev,map_inv]

theorem native_action (x : max4) : iota (nativeEquiv (coreAut x))=
    delta*iota (nativeEquiv x)*delta⁻¹ := by
  let f := iota.comp (nativeEquiv.toMonoidHom.comp coreAut.toMonoidHom)
  let g := (MulAut.conj delta).toMonoidHom.comp (iota.comp nativeEquiv.toMonoidHom)
  have he : f=g := by
    apply MonoidHom.eq_of_eqOn_dense coreBasis_generates
    rintro _ ⟨i,rfl⟩
    change iota (nativeEquiv (coreAut (coreBasis i)))=
      delta*iota (nativeEquiv (coreBasis i))*delta⁻¹
    rw [coreAut_basis,native_word,native_basis]
    calc
      iota (pi (slWord (actionWord i)))=
          (iota (pi (slWord (actionWord i)))*delta)*delta⁻¹ := by group
      _=(delta*iota (pi (slGen i)))*delta⁻¹ := by rw [← delta_action]
  exact congrArg (fun k : max4 →* PGammaL2 F => k x) he

theorem coreMap_conjugate (x : max4) : coreMap (coreAut x)=
    ⟨rotation*(coreMap x : candidateNormalizer)*rotation⁻¹,
      (inferInstance : normalizerCore.Normal).conj_mem _ (coreMap x).property rotation⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  change atlasEmbedding (hom x)=element*atlasEmbedding x*element⁻¹
  rw [← automorphism_apply,← element_action]
  exact atlasAction_apply element x

/-- The full normalizer is the actual mixed projective semilinear extension,
with the original native max4 marking and the specified outside actor. -/
theorem exists_normalizer_equiv_plus :
    ∃ e : candidateNormalizer ≃* Plus,
      (∀ x : max4, (e (coreMap x : candidateNormalizer)).val=
        iota (nativeEquiv x)) ∧ e rotation=outside := by
  let ec : normalizerCore ≃* pslCore := coreEquiv.trans pslCoreEquiv
  have hsq : (ec ⟨rotation^2,normalizerCore.sq_mem_of_index_two normalizerCore_index rotation⟩ : Plus)=
      outside^2 := by
    apply Subtype.ext
    change iota (coreEquiv ⟨rotation^2,
      normalizerCore.sq_mem_of_index_two normalizerCore_index rotation⟩)=delta^2
    rw [← coreMap_square,coreEquiv_apply_map,native_square,delta_square]
  have hact (n : normalizerCore) :
      (ec ⟨rotation*(n : candidateNormalizer)*rotation⁻¹,
        (inferInstance : normalizerCore.Normal).conj_mem n n.property rotation⟩ : Plus)=
      outside*(ec n : Plus)*outside⁻¹ := by
    obtain ⟨x,rfl⟩ := coreMap_bijective.surjective n
    apply Subtype.ext
    change iota (coreEquiv ⟨rotation*(coreMap x : candidateNormalizer)*rotation⁻¹,_⟩)=
      delta*iota (coreEquiv (coreMap x))*delta⁻¹
    rw [← coreMap_conjugate,coreEquiv_apply_map,coreEquiv_apply_map]
    exact native_action x
  obtain ⟨e,he,hr⟩ := exists_mulEquiv_of_index_two_extensions normalizerCore pslCore
    normalizerCore_index pslCore_index rotation outside rotation_not_mem_core outside_not_core ec hsq hact
  refine ⟨e,?_,hr⟩
  intro x
  rw [he (coreMap x)]
  change iota (coreEquiv (coreMap x))=iota (nativeEquiv x)
  rw [coreEquiv_apply_map]

end Tits.Max4Outer.Mixed
