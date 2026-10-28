module
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedCard
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# Two small factors of a symplectic Sylow seed

In the universal orthogonal cover, the second fixed layer projects to the
Sylow-invariant natural plane. Its displacement is exactly the singular
line above the natural fixed line. Passing through the original universal
cover quotient therefore splits the full fixed Sylow seed into the entire
central kernel and the intrinsic second-layer displacement. The former has
order at most q; the latter has order q and is disjoint from it.

The second factor is expressed by a commutator preimage, so simultaneous
normalizers of the layer and the selected Sylow preserve it. No complement
to the full fixed kernel in the whole cover is chosen.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two,
opening of (3.7), printed p.872; Aschbacher--Smith I.2.3 for the cover model.
-/

public noncomputable section
open Matrix Subgroup Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem standard_second_displacement (t : standard (K := K))
    (v : Space (K := K)) (hv : v.1 ∈ secondPlane) :
    action t.val v - v ∈ singularPoint := by
  have hfirst := (fixedModulo_firstLine v.1).mpr hv t
  have hplane : symplecticDerivedNatural 2 t.val v.1 ∈ secondPlane :=
    secondPlane_invariant t hv
  have hc : correction t.val.val v.1 = 0 := by
    have he := correction_square t.val.val v.1
    have hform (x : Natural (K := K)) : rowQuadratic x = ClassicalOrthogonal.formD 2 K x := by
      simp [ClassicalOrthogonal.formD_apply,rowQuadratic,Fin.sum_univ_two]
    simp only [hform] at he
    change ClassicalOrthogonal.formD 2 K (symplecticDerivedNatural 2 t.val v.1) =
      ClassicalOrthogonal.formD 2 K v.1 + correction t.val.val v.1 ^ 2 at he
    rw [secondPlane_formD _ hplane,secondPlane_formD _ hv,zero_add] at he
    exact (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp he.symm
  refine ⟨hfirst,?_⟩
  change (action t.val v).2-v.2=0
  rw [action_apply,hc]
  simp

private theorem standard_point_value (v : Space (K := K))
    (hv : v ∈ singularPoint) :
    ∃ t : standard (K := K), ∃ w : Space (K := K),
      w.1 ∈ secondPlane ∧ action t.val w-w=v := by
  refine ⟨pairedRoot 1 1, (v.1 (.inl 0) • ClassicalOrthogonal.e 1,0),?_,?_⟩
  · rw [secondPlane_eq_plane]
    intro i
    simp [ClassicalOrthogonal.e]
  · have hn : symplecticDerivedNatural 2 (pairedRoot (K := K) 1 1).val
        (v.1 (.inl 0) • ClassicalOrthogonal.e 1)-
        (v.1 (.inl 0) • ClassicalOrthogonal.e 1)=v.1 := by
      have hm := (mem_point_iff v.1).mp hv.1
      ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [pairedRoot, symplecticDerivedNatural_apply, rootElement, rootMatrix,
          Matrix.mul_apply,
          Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.single,
          Matrix.one_apply, ClassicalOrthogonal.e, hm.1,hm.2]
    have hs := standard_second_displacement (pairedRoot (K := K) 1 1)
      (v.1 (.inl 0) • ClassicalOrthogonal.e 1,0) (by
        rw [secondPlane_eq_plane]; intro i; simp [ClassicalOrthogonal.e])
    apply Prod.ext hn
    exact hs.2.trans hv.2.symm


private theorem moved_second_mem_iff (g : L (K := K)) (v : Space (K := K)) :
    projection v ∈ movedPlane g ↔
      ∀ t : movedSylow g, projection (action t.val v-v) ∈ movedLine g := by
  obtain ⟨w,rfl⟩ := (action (K := K)).apply_bijective g |>.surjective v
  have hmem (N : Submodule K (Natural (K := K))) (x : Space (K := K)) :
      projection (action g x) ∈ N.map (symplecticDerivedNatural 2 g) ↔ projection x ∈ N := by
    rw [projection.isIntertwining]
    constructor
    · rintro ⟨y,hy,he⟩
      exact ((symplecticDerivedNatural (k := K) 2).apply_bijective g).injective he ▸ hy
    · intro hx
      exact ⟨projection x,hx,rfl⟩
  change projection (action g w) ∈ (secondPlane (K := K)).map (symplecticDerivedNatural 2 g) ↔ _
  rw [hmem]
  constructor
  · intro hw t
    obtain ⟨a,ha,ht⟩ := t.property
    rw [←ht]
    change projection (action ((MulAut.conj g) a) (action g w)-action g w) ∈ _
    rw [Transport.conjugate_action,←map_sub]
    apply (hmem firstLine _).mpr
    exact (fixedModulo_firstLine w.1).mpr hw ⟨a,ha⟩
  · intro hw
    apply (fixedModulo_firstLine w.1).mp
    intro t
    have ht := hw ⟨(MulAut.conj g) t.val,⟨t.val,t.property,rfl⟩⟩
    change projection (action ((MulAut.conj g) t.val) (action g w)-action g w) ∈ _ at ht
    rw [Transport.conjugate_action,←map_sub] at ht
    exact (hmem firstLine _).mp ht

private theorem moved_second_displacement (g : L (K := K))
    (t : movedSylow g) (v : Space (K := K)) (hv : projection v ∈ movedPlane g) :
    action t.val v-v ∈ movedPoint g := by
  obtain ⟨a,ha,ht⟩ := t.property
  rw [←ht]
  obtain ⟨w,rfl⟩ := (action (K := K)).apply_bijective g |>.surjective v
  rw [projection.isIntertwining] at hv
  obtain ⟨x,hx,he⟩ := hv
  have hxw : x=projection w := ((symplecticDerivedNatural (k := K) 2).apply_bijective g).injective he
  subst x
  change action ((MulAut.conj g) a) (action g w)-action g w ∈ _
  rw [Transport.conjugate_action,←map_sub]
  exact ⟨_,standard_second_displacement ⟨a,ha⟩ w hx,rfl⟩

private theorem moved_point_value (g : L (K := K)) (v : Space (K := K))
    (hv : v ∈ movedPoint g) :
    ∃ t : movedSylow g, ∃ w : Space (K := K),
      projection w ∈ movedPlane g ∧ action t.val w-w=v := by
  obtain ⟨x,hx,rfl⟩ := hv
  obtain ⟨t,w,hw,he⟩ := standard_point_value x hx
  refine ⟨⟨(MulAut.conj g) t.val,⟨t.val,t.property,rfl⟩⟩,action g w,?_,?_⟩
  · refine ⟨projection w,hw,?_⟩
    rw [projection.isIntertwining]
  · change action ((MulAut.conj g) t.val) (action g w)-action g w=action g x
    rw [Transport.conjugate_action,←map_sub,he]

end Representation.SymplecticFourOrthogonalCover.SylowFlag

namespace Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement
variable {K W G : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
  {σ : Representation (ZMod 2) (L (K := K)) W}

/-- The full fixed Sylow seed is the product of its entire central kernel
and its intrinsic second-layer displacement, each of order at most q. -/
theorem embedded_sylow_seed_factors
    (U T A : Subgroup G) (j : Multiplicative W →* G)
    (hj : Function.Injective j) (hjU : j.range=U)
    (π : T →* L (K := K)) (S : Sylow 2 (L (K := K)))
    (hπ : π.range=(S : Subgroup (L (K := K))))
    (hact : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (π t) w))=
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (hA : ∀ w, j (Multiplicative.ofAdd w) ∈ A ↔ p w=0)
    (hAU : A ≤ U) :
    let B := U ⊓ centralizer (T : Set G)
    let X := commutatorPreimage U T B
    B=A ⊔ ⁅X,T⁆ ∧ Nat.card A ≤ Nat.card K ∧
      Nat.card (⁅X,T⁆ : Subgroup G)=Nat.card K ∧ Disjoint A ⁅X,T⁆ := by
  let B := U ⊓ centralizer (T : Set G)
  let X := commutatorPreimage U T B
  obtain ⟨g,hg⟩ := SylowFlag.exists_marking S
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let k : Multiplicative (Space (K := K)) →* G :=
    j.comp f.toLinearMap.toAddMonoidHom.toMultiplicative
  have hk (v : Space (K := K)) : k (Multiplicative.ofAdd v)=j (Multiplicative.ofAdd (f v)) := rfl
  have hkr : k.range=U := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr]
    · simpa only [MonoidHom.range_eq_map] using hjU
    · intro w
      obtain ⟨v,hv⟩ := hf w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg Multiplicative.ofAdd hv⟩
  have hUcomm : U ≤ centralizer (U : Set G) := by
    rintro x hx y hy
    obtain ⟨u,rfl⟩ := (hjU.symm ▸ hx : x ∈ j.range)
    obtain ⟨v,rfl⟩ := (hjU.symm ▸ hy : y ∈ j.range)
    rw [←map_mul,←map_mul,mul_comm]
  have hUB : U ≤ normalizer (B : Set G) :=
    (hUcomm.trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)
  have hfixed (v : Space (K := K)) : k (Multiplicative.ofAdd v) ∈ B ↔
      projection v ∈ SylowFlag.movedLine g := by
    have hfmem : k (Multiplicative.ofAdd v) ∈ B ↔
        f v ∈ fixed (σ.comp (S : Subgroup (L (K := K))).subtype) := by
      constructor
      · intro hv a
        obtain ⟨t,ht⟩ := (hπ.symm ▸ a.property : a.val ∈ π.range)
        apply Multiplicative.ofAdd.injective
        apply hj
        change j (Multiplicative.ofAdd (σ a.val (f v)))=j (Multiplicative.ofAdd (f v))
        rw [←ht,hact,←hk,hv.2 t.val t.property,mul_inv_cancel_right]
      · intro hv
        refine ⟨hkr ▸ ⟨_,rfl⟩,fun t ht => ?_⟩
        have hm : π ⟨t,ht⟩ ∈ (S : Subgroup (L (K := K))) := hπ ▸ ⟨_,rfl⟩
        have he := congrArg (fun w => j (Multiplicative.ofAdd w))
          (hv ⟨π ⟨t,ht⟩,hm⟩)
        change j (Multiplicative.ofAdd (σ (π ⟨t,ht⟩) (f v)))=j (Multiplicative.ofAdd (f v)) at he
        rw [hact,←hk,mul_inv_eq_iff_eq_mul] at he
        exact he
    rw [hfmem,cover_fixed_preimage p hp]
    change p (f v) ∈ fixed (binaryNatural.comp (S : Subgroup (L (K := K))).subtype) ↔ _
    rw [hpf,hg]
    exact SetLike.ext_iff.mp (SylowFlag.movedLine_fixed g) v.1
  have hdisp (t : T) (v : Space (K := K)) :
      k (Multiplicative.ofAdd (action (π t) v-v))=⁅t.val,k (Multiplicative.ofAdd v)⁆ := by
    rw [hk,map_sub]
    change j (Multiplicative.ofAdd (f (binaryAction (π t) v)-f v))=_
    rw [f.isIntertwining,ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  have hsecond (v : Space (K := K)) : k (Multiplicative.ofAdd v) ∈ X ↔
      projection v ∈ SylowFlag.movedPlane g := by
    rw [mem_commutatorPreimage_iff U T B hUB]
    have hu : k (Multiplicative.ofAdd v) ∈ U := hkr ▸ ⟨_,rfl⟩
    simp only [hu,true_and]
    rw [SylowFlag.moved_second_mem_iff]
    constructor
    · intro hv t
      have htS : t.val ∈ (S : Subgroup (L (K := K))) := hg.symm ▸ t.property
      obtain ⟨a,ha⟩ := (hπ.symm ▸ htS : t.val ∈ π.range)
      apply (hfixed _).mp
      rw [←ha,hdisp,←commutatorElement_inv]
      exact B.inv_mem (hv a.val a.property)
    · intro hv t ht
      have hm : π ⟨t,ht⟩ ∈ SylowFlag.movedSylow g := hg ▸ hπ ▸ ⟨_,rfl⟩
      have he := (hfixed _).mpr (hv ⟨π ⟨t,ht⟩,hm⟩)
      rw [hdisp,←commutatorElement_inv] at he
      exact B.inv_mem_iff.mp he
  let D := ((SylowFlag.movedPoint g).restrictScalars (ZMod 2)).toAddSubgroup.toSubgroup.map k
  have hD : ⁅X,T⁆=D := by
    rw [commutator_comm]
    apply le_antisymm
    · apply commutator_le.mpr
      intro t ht x hx
      obtain ⟨v,rfl⟩ := (hkr.symm ▸ commutatorPreimage_le U T B hx : x ∈ k.range)
      change ⁅t,k (Multiplicative.ofAdd v.toAdd)⁆ ∈ D
      rw [←hdisp ⟨t,ht⟩]
      exact mem_map_of_mem k (SylowFlag.moved_second_displacement g
        ⟨π ⟨t,ht⟩,hg ▸ hπ ▸ ⟨_,rfl⟩⟩ v.toAdd ((hsecond _).mp hx))
    · rintro x ⟨v,hv,rfl⟩
      obtain ⟨t,w,hw,he⟩ := SylowFlag.moved_point_value g v.toAdd hv
      obtain ⟨a,ha⟩ := (hπ.symm ▸ hg.symm ▸ t.property : t.val ∈ π.range)
      change k (Multiplicative.ofAdd v.toAdd) ∈ ⁅T,X⁆
      rw [←he,←ha,hdisp]
      exact commutator_mem_commutator a.property ((hsecond _).mpr hw)
  have hAimage : A=((radical (K := K)).restrictScalars (ZMod 2)).toAddSubgroup.toSubgroup.map k := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,rfl⟩ := (hkr.symm ▸ hAU hx : x ∈ k.range)
      have hv : v.toAdd.1=0 := by
        have he := (hA _).mp hx
        change p (f v.toAdd)=0 at he
        rwa [hpf] at he
      exact mem_map_of_mem k hv
    · rintro ⟨v,hv,rfl⟩
      apply (hA _).mpr
      change p (f v.toAdd)=0
      rw [hpf]
      exact hv
  have hsum : B=A ⊔ D := by
    apply le_antisymm
    · intro x hx
      obtain ⟨v,rfl⟩ := (hkr.symm ▸ hx.1 : x ∈ k.range)
      have hv : v.toAdd ∈ SylowFlag.movedPoint g ⊔ radical := by
        rw [←SylowFlag.movedLine_preimage]
        exact (hfixed _).mp hx
      obtain ⟨w,hw,z,hz,he⟩ := Submodule.mem_sup.mp hv
      have hwm : k (Multiplicative.ofAdd w) ∈ D := mem_map_of_mem k hw
      have hzm : k (Multiplicative.ofAdd z) ∈ A := by
        rw [hAimage]
        exact mem_map_of_mem k hz
      have hh := mul_mem (mem_sup_right hwm) (mem_sup_left hzm)
      rw [←map_mul,←ofAdd_add,he] at hh
      exact hh
    · apply sup_le
      · intro x hx
        obtain ⟨v,rfl⟩ := (hkr.symm ▸ hAU hx : x ∈ k.range)
        apply (hfixed _).mpr
        have he := (hA _).mp hx
        change p (f v.toAdd)=0 at he
        rw [hpf] at he
        change projection v.toAdd ∈ _
        rw [show projection v.toAdd=0 from he]
        exact Submodule.zero_mem _
      · rw [←hD]
        exact commutator_commutatorPreimage_le U T B hUB
  have hAc : Nat.card A ≤ Nat.card K := by
    rw [hAimage]
    apply (Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective k _)).trans_eq
    change Nat.card (radical (K := K))=Nat.card K
    rw [Module.natCard_eq_pow_finrank (K := K),radical_finrank,pow_one]
  have hiD : Function.Injective (fun v : SylowFlag.movedPoint g => k (Multiplicative.ofAdd v.val)) := by
    intro v w he
    have hfhe := Multiplicative.ofAdd.injective (hj he)
    have hn : projection (v.val-w.val)=0 := by
      have hh := congrArg p hfhe
      change p (f v.val)=p (f w.val) at hh
      rw [hpf,hpf] at hh
      exact map_sub projection v.val w.val |>.trans (sub_eq_zero.mpr hh)
    have hd : v.val-w.val ∈ (⊥ : Submodule K (Space (K := K))) :=
      (SylowFlag.movedPoint_disjoint g).le_bot ⟨(SylowFlag.movedPoint g).sub_mem v.property w.property,hn⟩
    exact Subtype.ext (sub_eq_zero.mp hd)
  have hDc : Nat.card D=Nat.card K := by
    have hbij : Function.Bijective
        (fun v : SylowFlag.movedPoint g => (⟨k (Multiplicative.ofAdd v.val),mem_map_of_mem k v.property⟩ : D)) := by
      refine ⟨fun v w he => hiD (congrArg Subtype.val he),?_⟩
      rintro ⟨x,⟨v,hv,rfl⟩⟩
      exact ⟨⟨v.toAdd,hv⟩,rfl⟩
    rw [←Nat.card_congr (Equiv.ofBijective _ hbij),
      Module.natCard_eq_pow_finrank (K := K),SylowFlag.movedPoint_finrank,pow_one]
  have hdis : Disjoint A D := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro x ⟨hx,⟨v,hv,rfl⟩⟩
    have hz := (hA _).mp hx
    change p (f v.toAdd)=0 at hz
    rw [hpf] at hz
    have hv0 : v.toAdd=0 := (SylowFlag.movedPoint_disjoint g).le_bot ⟨hv,hz⟩
    change k (Multiplicative.ofAdd v.toAdd)=1
    rw [hv0,ofAdd_zero,map_one]
  change B=A ⊔ ⁅X,T⁆ ∧ _
  rw [hD]
  exact ⟨hsum,hAc,hDc,hdis⟩

end Representation.SymplecticFourOrthogonalCover
