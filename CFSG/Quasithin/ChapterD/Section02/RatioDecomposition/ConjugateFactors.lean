module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Assembly
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import Mathlib.GroupTheory.Sylow

/-!
# Ambient permutation of the original ratio factors

Each indecomposable starred block is a conjugacy orbit once its starred
subgroups are Sylow two-subgroups. The two directions use Sylow conjugacy
inside the factor and normality of the embedded actor in the decomposed group.
An automorphism preserving the original starred family therefore permutes
whole blocks. Their generated actors and exact commutator supports follow.

For the literal normal Jhat action supplied by `FactorData`, ambient
conjugation preserves the starred family through the subgroup inclusion.
The resulting index permutations form a group homomorphism, and Jhat lies in
its kernel. `normalOddSeed_partition_action` applies this to the original
Sylow-fixed seed reduction, without introducing a uniqueness or invariance
premise. Its sole remaining classification input is the D.2.17 identification
of each indecomposable starred family with its Sylow two-subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, D.2.16–17,
printed pp.187–188, and original 15.1.2, first paragraph, printed pp.1084–1085
(1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u v

private theorem map_conj_hom {H G : Type*} [Group H] [Group G]
    (f : H →* G) (A : Subgroup H) (h : H) :
    (A.map (MulAut.conj h).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f h)).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

namespace Decomposition
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : Decomposition ρ)

theorem index_eq_of_mem_block {i j : d.Index} {A : Subgroup G}
    (hi : A ∈ d.block i) (hj : A ∈ d.block j) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (d.blocks_disjoint hij) hi hj

variable [FiniteDimensional (ZMod 2) V]

theorem block_map_conj (hf : Function.Injective ρ) {i : d.Index} {A : Subgroup G}
    (hA : A ∈ d.block i) (g : G) : A.map (MulAut.conj g).toMonoidHom ∈ d.block i := by
  have hstar : A ∈ QhatStar ρ := d.block_stars ▸ Set.mem_iUnion.mpr ⟨i,hA⟩
  have hcstar := QhatStar.map_conj ρ hstar g
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (d.block_stars.symm ▸ hcstar)
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ (d.factor i).actor := by
    let : (d.factor i).actor.Normal := d.actor_normal ρ hf i
    rw [← Subgroup.Normal.map_conj_eq (H := (d.factor i).actor) g]
    exact Subgroup.map_mono (by rw [← d.block_generates i]; exact le_sSup hA)
  have hle' : A.map (MulAut.conj g).toMonoidHom ≤ (d.factor j).actor := by
    rw [← d.block_generates j]
    exact le_sSup hj
  have he : j = i := by
    by_contra hji
    exact hcstar.1.2.1.1 (le_bot_iff.mp ((le_inf hle' hle).trans
      (d.actors_independent.pairwiseDisjoint hji).le_bot))
  exact he ▸ hj

omit [FiniteDimensional (ZMod 2) V] in
theorem block_conjugate
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action → ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    {i : d.Index} {A B : Subgroup G} (hA : A ∈ d.block i) (hB : B ∈ d.block i) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B := by
  obtain ⟨A,hA,rfl⟩ := hA
  obtain ⟨B,hB,rfl⟩ := hB
  obtain ⟨S,rfl⟩ := hsyl i A hA
  obtain ⟨T,rfl⟩ := hsyl i B hB
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (d.factor i).Carrier S T
  have he : (S : Subgroup (d.factor i).Carrier).map (MulAut.conj g).toMonoidHom = T := by
    exact congrArg Sylow.toSubgroup hg
  refine ⟨(d.factor i).embedding.groupMap g,?_⟩
  rw [← map_conj_hom,he]

private theorem image_block_exists (hf : Function.Injective ρ)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action → ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (e : G ≃* G)
    (hstars : ∀ A, A ∈ QhatStar ρ → A.map e.toMonoidHom ∈ QhatStar ρ)
    (i : d.Index) : ∃ j : d.Index, Subgroup.map e.toMonoidHom '' d.block i = d.block j := by
  obtain ⟨A,hA⟩ := d.block_nonempty i
  have hstar : A ∈ QhatStar ρ := d.block_stars ▸ Set.mem_iUnion.mpr ⟨i,hA⟩
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (d.block_stars.symm ▸ hstars A hstar)
  refine ⟨j,Set.ext fun B => ⟨?_,?_⟩⟩
  · rintro ⟨C,hC,rfl⟩
    obtain ⟨g,hg⟩ := d.block_conjugate hsyl hA hC
    rw [← hg,map_conj_hom]
    exact d.block_map_conj hf hj (e g)
  · intro hB
    obtain ⟨g,hg⟩ := d.block_conjugate hsyl hj hB
    refine ⟨A.map (MulAut.conj (e.symm g)).toMonoidHom,
      d.block_map_conj hf hA (e.symm g),?_⟩
    rw [map_conj_hom]
    simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hg

theorem permutes_blocks (hf : Function.Injective ρ)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (e : G ≃* G)
    (hstars : ∀ A, A ∈ QhatStar ρ ↔ A.map e.toMonoidHom ∈ QhatStar ρ) :
    ∃ p : Equiv.Perm d.Index,
      ∀ i, Subgroup.map e.toMonoidHom '' d.block i = d.block (p i) := by
  classical
  have hex := d.image_block_exists hf (fun i A => (hsyl i A).mp) e (fun A => (hstars A).mp)
  choose f h using hex
  have hf' : Function.Injective f := by
    intro i j hij
    obtain ⟨A,hA⟩ := d.block_nonempty i
    have hAi : A.map e.toMonoidHom ∈ d.block (f i) := h i ▸ Set.mem_image_of_mem _ hA
    rw [hij,← h j] at hAi
    obtain ⟨B,hB,hBA⟩ := hAi
    have he : B = A := (Subgroup.map_injective e.injective) hBA
    exact d.index_eq_of_mem_block hA (he ▸ hB)
  exact ⟨Equiv.ofBijective f ⟨hf',Finite.surjective_of_injective hf'⟩,h⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem actor_map_of_block (e : G ≃* G) {i j : d.Index}
    (h : Subgroup.map e.toMonoidHom '' d.block i = d.block j) :
    (d.factor i).actor.map e.toMonoidHom = (d.factor j).actor := by
  have he := congrArg sSup h
  rw [sSup_image] at he
  simp only [← Subgroup.map_iSup] at he
  rw [← sSup_eq_iSup,d.block_generates,d.block_generates] at he
  exact he

omit [FiniteDimensional (ZMod 2) V] in
theorem support_map_of_actor (e : G ≃* G) (E : V ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (ρ g v) = ρ (e g) (E v)) {i j : d.Index}
    (h : (d.factor i).actor.map e.toMonoidHom = (d.factor j).actor) :
    (d.factor i).space.map E.toLinearMap = (d.factor j).space := by
  rw [Factor.space_eq_support,Factor.space_eq_support]
  have he : ∀ g v, ρ g (E.symm v) = E.symm (ρ (e g) v) := by
    intro g v
    apply E.injective
    rw [hE,E.apply_symm_apply,E.apply_symm_apply]
  have hh := subspaceCommutator_map_embedding ρ ρ e.toMonoidHom E.symm.toLinearMap
    he (d.factor i).actor ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr E.symm.surjective,h] at hh
  rw [hh,← Submodule.map_comp]
  simp only [LinearEquiv.comp_coe,LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap,Submodule.map_id]


end Decomposition
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private theorem map_conjNormal {K : Subgroup G} [K.Normal]
    (A : Subgroup K) (g : G) :
    (A.map (MulAut.conjNormal g).toMonoidHom).map K.subtype =
      (A.map K.subtype).map (MulAut.conj g).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1

namespace FactorData
variable {ρ} {K : Subgroup G} {U : Submodule (ZMod 2) V} (c : FactorData ρ K U)

@[expose] def ambientBlock (d : Decomposition c.representation) (i : d.Index) :
    Set (Subgroup G) := (Subgroup.map K.subtype) '' d.block i

@[expose] def ambientFactor (d : Decomposition c.representation) (i : d.Index) : Factor ρ :=
  (d.factor i).map (c.embedding ρ)

omit [FiniteDimensional (ZMod 2) V] in
theorem ambientBlock_stars (hK : K = Jhat ρ) (d : Decomposition c.representation) :
    (⋃ i, c.ambientBlock d i) = QhatStar ρ := by
  ext A
  constructor
  · intro hA
    obtain ⟨i,B,hB,rfl⟩ := Set.mem_iUnion.mp hA
    exact (c.stars B).mp (d.block_stars ▸ Set.mem_iUnion.mpr ⟨i,hB⟩)
  · intro hA
    have hAK : A ≤ K := hK.symm ▸ le_sSup hA
    have hB : A.subgroupOf K ∈ QhatStar c.representation := by
      apply (c.stars _).mpr
      rwa [Subgroup.map_subgroupOf_eq_of_le hAK]
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (d.block_stars.symm ▸ hB)
    exact Set.mem_iUnion.mpr ⟨i,A.subgroupOf K,hi,map_subgroupOf_eq_of_le hAK⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem ambientBlock_nonempty (d : Decomposition c.representation) (i : d.Index) :
    (c.ambientBlock d i).Nonempty := (d.block_nonempty i).image _

omit [FiniteDimensional (ZMod 2) V] in
theorem ambientBlock_index_eq (d : Decomposition c.representation) {i j : d.Index}
    {A : Subgroup G} (hi : A ∈ c.ambientBlock d i) (hj : A ∈ c.ambientBlock d j) : i = j := by
  obtain ⟨B,hB,rfl⟩ := hi
  obtain ⟨C,hC,hCB⟩ := hj
  have he : C = B := Subgroup.map_injective K.subtype_injective hCB
  exact d.index_eq_of_mem_block hB (he ▸ hC)

theorem conjNormal_stars [K.Normal] (g : G) (A : Subgroup K) :
    A ∈ QhatStar c.representation ↔
      A.map (MulAut.conjNormal g).toMonoidHom ∈ QhatStar c.representation := by
  have hforward (g : G) (A : Subgroup K) (hA : A ∈ QhatStar c.representation) :
      A.map (MulAut.conjNormal g).toMonoidHom ∈ QhatStar c.representation := by
    apply (c.stars _).mpr
    rw [map_conjNormal]
    exact QhatStar.map_conj ρ ((c.stars A).mp hA) g
  constructor
  · exact hforward g A
  · intro hA
    have hh := hforward g⁻¹ _ hA
    rw [map_inv,Subgroup.map_map] at hh
    have he : ((MulAut.conjNormal g : MulAut K)⁻¹).toMonoidHom.comp
        (MulAut.conjNormal g).toMonoidHom = MonoidHom.id K := by
      apply MonoidHom.ext
      intro x
      exact MulEquiv.symm_apply_apply (MulAut.conjNormal g) x
    simpa only [he,Subgroup.map_id] using hh

theorem ambient_permutation [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (g : G) : ∃ p : Equiv.Perm d.Index, ∀ i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (p i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom = (c.ambientFactor d (p i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (p i)).space := by
  obtain ⟨p,hp⟩ := d.permutes_blocks c.faithful hsyl (MulAut.conjNormal g) (c.conjNormal_stars g)
  refine ⟨p,fun i => ?_⟩
  have hactor : (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (p i)).actor := by
    simp only [ambientFactor,Factor.map_actor,FactorData.embedding]
    rw [← map_conjNormal,d.actor_map_of_block _ (hp i)]
  refine ⟨?_,hactor,?_⟩
  · change Subgroup.map (MulAut.conj g).toMonoidHom ''
        (Subgroup.map K.subtype '' d.block i) = Subgroup.map K.subtype '' d.block (p i)
    rw [← hp i,Set.image_image,Set.image_image]
    congr 1
    funext A
    exact (map_conjNormal A g).symm
  · rw [Factor.space_eq_support,Factor.space_eq_support,moved_map_conjugate,hactor]

omit [FiniteDimensional (ZMod 2) V] in
theorem ambientBlock_injective (d : Decomposition c.representation) :
    Function.Injective (c.ambientBlock d) := by
  intro i j hij
  obtain ⟨A,hA⟩ := c.ambientBlock_nonempty d i
  exact c.ambientBlock_index_eq d hA (hij ▸ hA)

noncomputable def ambientPermutation [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (g : G) : Equiv.Perm d.Index := (c.ambient_permutation d hsyl g).choose

theorem ambientPermutation_spec [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (g : G) (i : d.Index) :
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i =
        c.ambientBlock d (c.ambientPermutation d hsyl g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (c.ambientPermutation d hsyl g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (c.ambientPermutation d hsyl g i)).space :=
  (c.ambient_permutation d hsyl g).choose_spec i

noncomputable def ambientAction [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A) :
    G →* Equiv.Perm d.Index where
  toFun := c.ambientPermutation d hsyl
  map_one' := by
    ext i
    apply c.ambientBlock_injective d
    rw [← (c.ambientPermutation_spec d hsyl 1 i).1]
    have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [he]
    simp only [Subgroup.map_id,Equiv.Perm.one_apply]
    exact Set.image_id _
  map_mul' g h := by
    ext i
    apply c.ambientBlock_injective d
    change c.ambientBlock d (c.ambientPermutation d hsyl (g*h) i) =
      c.ambientBlock d (c.ambientPermutation d hsyl g (c.ambientPermutation d hsyl h i))
    rw [← (c.ambientPermutation_spec d hsyl (g*h) i).1,
      ← (c.ambientPermutation_spec d hsyl g (c.ambientPermutation d hsyl h i)).1,
      ← (c.ambientPermutation_spec d hsyl h i).1,Set.image_image]
    congr 1
    funext A
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]

theorem ambientAction_spec [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (g : G) (i : d.Index) :
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i =
        c.ambientBlock d (c.ambientAction d hsyl g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (c.ambientAction d hsyl g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (c.ambientAction d hsyl g i)).space :=
  c.ambientPermutation_spec d hsyl g i

omit [FiniteDimensional (ZMod 2) V] in
theorem ambientBlock_generates (d : Decomposition c.representation) (i : d.Index) :
    sSup (c.ambientBlock d i) = (c.ambientFactor d i).actor := by
  rw [ambientBlock,sSup_image]
  simp only [← Subgroup.map_iSup]
  rw [← sSup_eq_iSup,d.block_generates]
  exact (Factor.map_actor (d.factor i) (c.embedding ρ)).symm

omit [FiniteDimensional (ZMod 2) V] in
theorem ambientBlocks_disjoint (d : Decomposition c.representation) :
    Pairwise (fun i j => Disjoint (c.ambientBlock d i) (c.ambientBlock d j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr fun _ hi hj => hij (c.ambientBlock_index_eq d hi hj)

theorem ambientAction_fixed_by_subgroup [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (k : K) (i : d.Index) : c.ambientAction d hsyl (k:G) i = i := by
  obtain ⟨A,hA⟩ := d.block_nonempty i
  have hA' : A.map K.subtype ∈ c.ambientBlock d i := ⟨A,hA,rfl⟩
  have hm : (A.map K.subtype).map (MulAut.conj (k:G)).toMonoidHom ∈
      c.ambientBlock d (c.ambientAction d hsyl (k:G) i) :=
    (c.ambientAction_spec d hsyl (k:G) i).1 ▸ Set.mem_image_of_mem _ hA'
  have hm' : (A.map K.subtype).map (MulAut.conj (k:G)).toMonoidHom ∈
      c.ambientBlock d i := by
    have he := map_conj_hom K.subtype A k
    change (A.map (MulAut.conj k).toMonoidHom).map K.subtype =
      (A.map K.subtype).map (MulAut.conj (k:G)).toMonoidHom at he
    rw [← he]
    exact ⟨_,d.block_map_conj c.faithful hA k,rfl⟩
  exact c.ambientBlock_index_eq d hm hm'

theorem subgroup_le_ambientAction_ker [K.Normal] (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A) :
    K ≤ (c.ambientAction d hsyl).ker := by
  intro k hk
  apply MonoidHom.mem_ker.mpr
  ext i
  exact c.ambientAction_fixed_by_subgroup d hsyl ⟨k,hk⟩ i

/-- The original Jhat partition carries the actual ambient action, with the
same actors and commutator supports through the literal subgroup inclusion. -/
theorem source_Jhat_partition_action (hK : K = Jhat ρ)
    (d : Decomposition c.representation)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A) :
    ∃ π : G →* Equiv.Perm d.Index,
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ K ≤ π.ker ∧ ∀ g i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom = (c.ambientFactor d (π g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space := by
  let : K.Normal := by rw [hK]; exact Jhat_normal ρ
  exact ⟨c.ambientAction d hsyl,c.ambientBlock_stars hK d,
    c.subgroup_le_ambientAction_ker d hsyl,c.ambientAction_spec d hsyl⟩

end FactorData

/-- The original seed reduction supplies the literal normal-Jhat data consumed
by the ambient factor action. Only the D.2.17 local Sylow conclusion remains
as classification input. -/
theorem normalOddSeed_partition_action [Finite G] (hf : Function.Injective ρ)
    (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    (hK : K = Jhat ρ) (hne : (QhatStar ρ).Nonempty) :
    let c := normalOddFactorData ρ hf K P S hodd hKP Z hZ hgen hK hne
    ∀ (d : Decomposition c.representation),
      (∀ i (A : Subgroup (d.factor i).Carrier), A ∈ QhatStar (d.factor i).action ↔
        ∃ T : Sylow 2 (d.factor i).Carrier, (T : Subgroup _) = A) →
    ∃ π : G →* Equiv.Perm d.Index,
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ K ≤ π.ker ∧ ∀ g i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom = (c.ambientFactor d (π g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space := by
  intro c d hsyl
  exact FactorData.source_Jhat_partition_action c hK d hsyl

end CFSG.Quasithin.ChapterD.RatioDecomposition
