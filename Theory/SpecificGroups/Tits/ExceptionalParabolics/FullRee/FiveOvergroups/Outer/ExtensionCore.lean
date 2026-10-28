module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Normalizer
/-! The actual max4 core has index two in its fixed full-Ree normalizer.
Its specified PSL₂ equivalence and two generators are retained for the
outer extension comparison; the order-eight rotation lies outside the core.
Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

@[expose] public section
open Subgroup
noncomputable section
namespace Tits.Max4Outer
open MinimumIndexCandidates ExceptionalParabolics.FullRee
open ExceptionalParabolics.FullRee.FiveOvergroups

def normalizerCore : Subgroup candidateNormalizer := candidate.subgroupOf candidateNormalizer

instance normalizerCore_normal : normalizerCore.Normal := by
  dsimp [normalizerCore,candidateNormalizer]
  exact normal_subgroupOf_of_le_normalizer le_rfl

def coreMap : max4 →* normalizerCore where
  toFun x := ⟨⟨atlasEmbedding x,
    candidate.le_normalizer (mem_map_of_mem atlasEmbedding x.property)⟩,
      mem_map_of_mem atlasEmbedding x.property⟩
  map_one' := by apply Subtype.ext;apply Subtype.ext;exact atlasEmbedding.map_one
  map_mul' x y := by apply Subtype.ext;apply Subtype.ext;exact atlasEmbedding.map_mul x y

theorem coreMap_bijective : Function.Bijective coreMap := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply atlasEmbedding_injective
    exact congrArg (fun z : normalizerCore => (z.val : ReeF4.Model 0)) he
  · intro x
    obtain ⟨y,hy,he⟩ := x.property
    refine ⟨⟨y,hy⟩,?_⟩
    apply Subtype.ext
    exact Subtype.ext he

def coreEquiv : normalizerCore ≃* Max4Projective.PSL :=
  (MulEquiv.ofBijective coreMap coreMap_bijective).symm.trans Max4Projective.nativeEquiv

theorem coreEquiv_apply_map (x : max4) : coreEquiv (coreMap x)=Max4Projective.nativeEquiv x := by
  change Max4Projective.nativeEquiv ((MulEquiv.ofBijective coreMap coreMap_bijective).symm
    ((MulEquiv.ofBijective coreMap coreMap_bijective) x))=_
  rw [MulEquiv.symm_apply_apply]

theorem normalizerCore_card : Nat.card normalizerCore=7800 :=
  (Nat.card_congr coreEquiv.toEquiv).trans Max4Projective.projective_card

theorem normalizerCore_index : normalizerCore.index=2 := by
  have h := normalizerCore.card_mul_index
  rw [normalizerCore_card,normalizer_card] at h
  omega

theorem reflector_mem_core : reflector∈normalizerCore :=
  mem_map_of_mem atlasEmbedding (eval_core_mem reflectionWord)

theorem rotation_not_mem_core : rotation∉normalizerCore := by
  intro hr
  have hle : sixteen≤normalizerCore := sup_le (zpowers_le.mpr hr)
    (zpowers_le.mpr reflector_mem_core)
  have hd := card_dvd_of_le hle
  rw [sixteen_spec.1,normalizerCore_card] at hd
  norm_num at hd

def coreBasis (i : Fin 2) : max4 := ⟨coreGen i,coreGen_mem i⟩

theorem coreBasis_generates : closure (Set.range coreBasis)=⊤ := by
  apply map_injective max4.subtype_injective
  rw [MonoidHom.map_closure,← MonoidHom.range_eq_map,max4.range_subtype]
  have hs : max4.subtype '' Set.range coreBasis=Set.range coreGen := by
    ext x
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩;exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩;exact ⟨coreBasis i,⟨i,rfl⟩,rfl⟩
  rw [hs]
  have hr : Set.range coreGen={max4Generators.1,max4Generators.2} := by
    ext x
    simp [coreGen,or_comm]
  rw [hr]
  rfl

def coreAut : MulAut max4 :=
  (automorphism.subgroupMap max4).trans (MulEquiv.subgroupCongr automorphism_preserves)

theorem coreAut_val (x : max4) : (coreAut x).val=hom x := rfl

theorem eval_basis_val (w : List (Fin 2 × Bool)) : (eval coreBasis w).val=eval coreGen w := by
  change max4.subtype (eval coreBasis w)=_
  exact map_eval max4.subtype coreBasis w

theorem coreAut_basis (i : Fin 2) : coreAut (coreBasis i)=eval coreBasis (actionWord i) := by
  apply Subtype.ext
  rw [coreAut_val,eval_basis_val]
  exact hom_coreGen i

theorem square_mem : squareElement∈max4 := max4.inv_mem (eval_core_mem squareWord)

theorem coreMap_square : coreMap ⟨squareElement,square_mem⟩=
    ⟨rotation^2,normalizerCore.sq_mem_of_index_two normalizerCore_index rotation⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  exact element_square.symm

end Tits.Max4Outer
