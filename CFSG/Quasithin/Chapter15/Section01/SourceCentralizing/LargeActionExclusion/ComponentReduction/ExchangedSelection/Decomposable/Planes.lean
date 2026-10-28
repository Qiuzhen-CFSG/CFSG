module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.Decomposable
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# The original two dihedral supports and their Sylow exchange

The ratio-two decomposition has two four-dimensional supports. Their literal
inclusions give complementary subgroups of order sixteen in the original V.
The embedded odd kernel of each factor moves exactly its own support and
fixes exactly the other one. The same prime, three or five, is retained in
both factor markings. Each marked involution has a fixed subgroup of order
four inside its own support.

The original factor permutation identifies the support stabilizer in T
with the kernel of its nontrivial action on two indices. Thus it is normal
of index two and every element outside it exchanges the actual supports.
`supportPair_of_decomposable` applies these facts to the original classified
action. Identifying the Thompson marker and its centralizer residual remains
a separate source calculation; no such identification is assumed here.

Source: Aschbacher--Smith 15.1.7(6), 15.1.16(a), and 15.1.24(1),
printed pp.1087--1088, 1092, and 1101.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

def plane (V : Subgroup G) [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  (binarySubgroup W).map V.subtype

omit [Finite G] in
theorem plane_le {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : plane V W ≤ V := map_subtype_le _

omit [Finite G] in
theorem plane_injective (V : Subgroup G) [IsElementaryAbelian 2 V] :
    Function.Injective (plane V) := by
  intro A B h
  have he := Subgroup.map_injective V.subtype_injective h
  ext v
  change v.toMul ∈ binarySubgroup A ↔ v.toMul ∈ binarySubgroup B
  rw [he]

theorem plane_card {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) :
    Nat.card (plane V W) = 2 ^ Module.finrank (ZMod 2) W := by
  rw [plane,card_map_of_injective V.subtype_injective,binarySubgroup_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]

omit [Finite G] in
theorem plane_conjugate {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V)) (t : M) :
    (plane V W).map (MulAut.conj (t : G)).toMonoidHom =
      plane V (W.map (imageRepresentation M V hn ((actionHom M V hn).rangeRestrict t))) := by
  ext x
  constructor
  · rintro ⟨y,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨(imageRepresentation M V hn ((actionHom M V hn).rangeRestrict t)
      (Additive.ofMul v)).toMul,?_,rfl⟩
    exact ⟨Additive.ofMul v,hv,rfl⟩
  · rintro ⟨v,⟨w,hw,he⟩,rfl⟩
    refine ⟨(w.toMul : G),⟨w.toMul,hw,rfl⟩,?_⟩
    exact congrArg (fun a : Additive V => (a.toMul : G)) he

omit [Finite G] in
theorem plane_complements {V : Subgroup G} [IsElementaryAbelian 2 V]
    {A B : Submodule (ZMod 2) (Additive V)} (h : IsCompl A B) :
    plane V A ⊔ plane V B = V ∧ plane V A ⊓ plane V B = ⊥ := by
  constructor
  · apply le_antisymm (sup_le (plane_le A) (plane_le B))
    intro v hv
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp
      (show Additive.ofMul (⟨v,hv⟩ : V) ∈ A ⊔ B by rw [h.sup_eq_top]; trivial)
    have he' := congrArg (fun w : Additive V => (w.toMul : G)) he
    change (a.toMul : G) * b.toMul = v at he'
    exact he' ▸ (plane V A ⊔ plane V B).mul_mem
      ((show plane V A ≤ plane V A ⊔ plane V B from le_sup_left) (mem_map_of_mem V.subtype ha))
      ((show plane V B ≤ plane V A ⊔ plane V B from le_sup_right) (mem_map_of_mem V.subtype hb))
  · apply bot_unique
    rintro v ⟨⟨a,ha,he⟩,⟨b,hb,hb'⟩⟩
    have hab : a = b := Subtype.ext (he.trans hb'.symm)
    have hz := Submodule.disjoint_def.mp h.disjoint (Additive.ofMul a) ha (hab.symm ▸ hb)
    have he' : (a : G) = 1 := congrArg (fun w : Additive V => (w.toMul : G)) hz
    exact he.symm.trans he'

/-- Ratio two forces the fixed half of the original marked involution to
have dimension two, including when the retained dihedral prime is five. -/
theorem marked_fixed_dimension {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (l : CyclicSource.LocalGeneration ρ)
    (hq : cubicRatio ρ = 2) (hd : Module.finrank (ZMod 2) W = 4) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers l.involution)) = 2 := by
  obtain ⟨he,hr,hquad,hhalf⟩ := involution_actor_rank_and_fixedCodim ρ l.involution l.order_two
  have hlo : cubicRatio ρ ≤ actionRatio ρ (zpowers l.involution) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he,isCubic_of_isQuadratic hquad⟩ le_rfl)
  rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hlo
  have hlo' : 2 ≤ fixedCodim ρ (zpowers l.involution) := by exact_mod_cast hlo
  have hsum := fixedCodim_add_finrank ρ (zpowers l.involution)
  omega

/-- The four-element fixed subgroup is formed using the literal factor
embedding and its marked involution. No Sylow marking is inferred here. -/
theorem embedded_marked_four {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (F : Factor (imageRepresentation M V hn))
    (l : CyclicSource.LocalGeneration F.action)
    (hq : cubicRatio (imageRepresentation M V hn) = 2)
    (hd : Module.finrank (ZMod 2) F.Space = 4) :
    let Z := (fixedSpace F.action (zpowers l.involution)).map F.embedding.spaceMap
    Nat.card (plane V Z) = 4 ∧
      Z = F.space ⊓ fixedSpace (imageRepresentation M V hn)
        ((zpowers l.involution).map F.embedding.groupMap) := by
  intro Z
  have hdim := marked_fixed_dimension l (F.embedding.ratio.trans hq) hd
  constructor
  · have he := (Submodule.equivMapOfInjective F.embedding.spaceMap
      F.embedding.space_injective (fixedSpace F.action (zpowers l.involution))).finrank_eq
    rw [plane_card,←he,hdim]
    norm_num
  · apply le_antisymm
    · exact le_inf (by rintro _ ⟨v,_,rfl⟩; exact ⟨v,rfl⟩)
        (F.embedding.map_fixed _ _ le_rfl)
    · rintro v ⟨⟨w,rfl⟩,hw⟩
      refine ⟨w,?_,rfl⟩
      intro g
      apply F.embedding.space_injective
      change F.embedding.spaceMap (F.action (g : F.Carrier) w) = F.embedding.spaceMap w
      rw [F.embedding.equivariant]
      exact hw ⟨F.embedding.groupMap g,mem_map_of_mem _ g.property⟩

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

private theorem perm_pair_fixed_iff_one {I : Type*} (i j : I) (hij : i ≠ j)
    (hall : ∀ k, k = i ∨ k = j) (p : Equiv.Perm I) : p i = i ↔ p = 1 := by
  refine ⟨?_,fun h => h ▸ rfl⟩
  intro hi
  have hj : p j = j := by
    rcases hall (p j) with h | h
    · exact False.elim (hij (p.injective (hi.trans h.symm)))
    · exact h
  ext k
  rcases hall k with rfl | rfl
  · exact hi
  · exact hj

omit [Finite G] in
/-- The actual Sylow subgroup has an index-two normal support stabilizer;
every element outside it exchanges the same two embedded planes. -/
theorem support_exchange {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (i j : d.Index) (hij : i ≠ j) (hall : ∀ k, k = i ∨ k = j)
    (t : M) (ht : (t : G) ∈ (T : Subgroup G))
    (htij : π ((actionHom M V hn).rangeRestrict t) i = j) :
    let V1 := plane V (c.ambientFactor d i).space
    let V2 := plane V (c.ambientFactor d j).space
    let S := (T : Subgroup G) ⊓ normalizer (V1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧
      (S.subgroupOf (T : Subgroup G)).Normal ∧
      S ≤ normalizer (V2 : Set G) ∧
      ∀ x ∈ (T : Subgroup G), x ∉ S →
        V1.map (MulAut.conj x).toMonoidHom = V2 ∧
        V2.map (MulAut.conj x).toMonoidHom = V1 := by
  classical
  intro V1 V2 S
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let a : (T : Subgroup G) →* Equiv.Perm d.Index := π.comp (f.comp (inclusion hTM))
  have hinj := (c.ambient_spaces_independent d).injective (c.ambient_space_ne_bot d)
  have hnormal (x : M) (k : d.Index) :
      (x : G) ∈ normalizer (plane V (c.ambientFactor d k).space : Set G) ↔
        π (f x) k = k := by
    have he : (plane V (c.ambientFactor d k).space).map (MulAut.conj (x : G)).toMonoidHom =
        plane V (c.ambientFactor d (π (f x) k)).space :=
      (plane_conjugate hn (c.ambientFactor d k).space x).trans
        (congrArg (plane V) (hs (f x) k))
    rw [MulEquiv.toMonoidHom_eq_coe] at he
    rw [mem_normalizer_iff_map_conj_eq,he]
    exact (plane_injective V).eq_iff.trans hinj.eq_iff
  have hker : S.subgroupOf (T : Subgroup G) = a.ker := by
    ext x
    change ((x : G) ∈ (T : Subgroup G) ∧ (x : G) ∈ normalizer (V1 : Set G)) ↔ a x = 1
    rw [and_iff_right x.property]
    exact (hnormal ⟨x,hTM x.property⟩ i).trans (perm_pair_fixed_iff_one i j hij hall (a x))
  have hI : Nat.card d.Index = 2 := by
    refine Nat.card_eq_two_iff.mpr ⟨i,j,hij,?_⟩
    exact Set.eq_univ_iff_forall.mpr (fun k => by simpa using hall k)
  have hcard : Nat.card a.range = 2 := by
    have hdvd := card_subgroup_dvd_card a.range
    rw [Nat.card_perm,hI] at hdvd
    have hne : a.range ≠ ⊥ := by
      intro hb
      have he : a ⟨t,ht⟩ = 1 := by
        simpa only [hb,mem_bot] using (show a ⟨t,ht⟩ ∈ a.range from ⟨⟨t,ht⟩,rfl⟩)
      have hi : π (f t) i = i := congrArg (fun q : Equiv.Perm d.Index => q i) he
      exact hij (hi.symm.trans htij)
    have hc := (Nat.dvd_prime Nat.prime_two).mp hdvd
    rcases hc with hc | hc
    · exact False.elim (hne ((Subgroup.card_eq_one).mp hc))
    · exact hc
  refine ⟨?_,?_,?_,?_⟩
  · change (S.subgroupOf (T : Subgroup G)).index = 2
    rw [hker,index_ker,hcard]
  · rw [hker]
    infer_instance
  · intro x hx
    have he : a ⟨x,hx.1⟩ = 1 := by
      change (⟨x,hx.1⟩ : (T : Subgroup G)) ∈ a.ker
      rw [←hker]
      exact hx
    apply (hnormal ⟨x,hTM hx.1⟩ j).mpr
    exact congrArg (fun q : Equiv.Perm d.Index => q j) he
  · intro x hx hxS
    let y : M := ⟨x,hTM hx⟩
    have hi : π (f y) i ≠ i := fun he => hxS ⟨hx,(hnormal y i).mpr he⟩
    have hij' : π (f y) i = j := (hall _).resolve_left hi
    have hji' : π (f y) j = i := by
      rcases hall (π (f y) j) with h | h
      · exact h
      · exact False.elim (hij ((π (f y)).injective (hij'.trans h.symm)))
    constructor
    · exact (plane_conjugate hn _ y).trans (congrArg (plane V) ((hs (f y) i).trans
        (congrArg (fun k => (c.ambientFactor d k).space) hij')))
    · exact (plane_conjugate hn _ y).trans (congrArg (plane V) ((hs (f y) j).trans
        (congrArg (fun k => (c.ambientFactor d k).space) hji')))

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
public section
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem embedded_kernel_moved {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (F : Factor ρ) (l : CyclicSource.LocalGeneration F.action) :
    subspaceCommutator ρ ⊤ (l.kernel.map F.embedding.groupMap) = F.space := by
  have hm : l.kernel.map F.embedding.groupMap ≤ F.actor := map_le_range _ _
  have hm' : subspaceCommutator ρ ⊤ (l.kernel.map F.embedding.groupMap) ≤
      subspaceCommutator ρ ⊤ F.actor := by
    apply Submodule.span_mono
    rintro _ ⟨g,hg,w,hw,rfl⟩
    exact ⟨g,hm hg,w,hw,rfl⟩
  apply le_antisymm (hm'.trans F.embedding.moved_le_range)
  have he := subspaceCommutator_map_embedding (ρ.comp F.embedding.groupMap) F.action
    (MonoidHom.id F.Carrier) F.embedding.spaceMap
    (fun g w => (F.embedding.equivariant g w).symm) l.kernel ⊤
  simp only [Subgroup.map_id,Submodule.map_top,l.moved] at he
  rw [subspaceCommutator_comp_map] at he
  exact he.ge.trans (subspaceCommutator_mono_left ρ le_top _)

theorem embedded_kernel_fixed {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W}
    (F : Factor ρ) (l : CyclicSource.LocalGeneration F.action)
    (B : Submodule (ZMod 2) W) (hB : B ≤ fixedSpace ρ F.actor)
    (hc : IsCompl B F.space) :
    fixedSpace ρ (l.kernel.map F.embedding.groupMap) = B := by
  have hodd : Odd (Nat.card (l.kernel.map F.embedding.groupMap)) := by
    rw [card_map_of_injective F.embedding.group_injective]
    let : Fact l.prime.Prime := ⟨l.prime_prime⟩
    obtain ⟨n,hn⟩ := l.pgroup.exists_card_eq
    rw [hn]
    exact l.prime_odd.pow
  have hp : IsCompl (fixedSpace ρ (l.kernel.map F.embedding.groupMap)) F.space := by
    rw [←embedded_kernel_moved F l]
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  apply (Submodule.eq_of_le_of_finrank_eq
    (hB.trans (fixedSpace_antitone ρ (map_le_range _ _))) ?_).symm
  have hdim1 := Submodule.finrank_add_eq_of_isCompl hc
  have hdim2 := Submodule.finrank_add_eq_of_isCompl hp
  omega

/-- Literal supports and odd kernels of the two original dihedral factors.
The fixed half of a chosen local involution is recorded separately from the
source's as-yet-unconstructed Thompson marker. -/
structure SupportPair {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) where
  first : d.Index
  second : d.Index
  distinct : first ≠ second
  covers : ∀ k, k = first ∨ k = second
  prime : ℕ
  prime_cases : prime = 3 ∨ prime = 5
  marking : ∀ k, CyclicSource.LocalGeneration (d.factor k).action
  dihedral : ∀ k, CyclicSource.DihedralMarking (marking k) prime 2
  support_card : ∀ k, Nat.card (plane V (c.ambientFactor d k).space) = 16
  marked_card : ∀ k, Nat.card (plane V
    ((fixedSpace (d.factor k).action (zpowers (marking k).involution)).map
      (c.ambientFactor d k).embedding.spaceMap)) = 4
  complement :
    plane V (c.ambientFactor d first).space ⊔ plane V (c.ambientFactor d second).space = V
  disjoint :
    plane V (c.ambientFactor d first).space ⊓ plane V (c.ambientFactor d second).space = ⊥
  kernel_card : ∀ k, Nat.card ((marking k).kernel.map
    (c.ambientFactor d k).embedding.groupMap) = prime
  kernel_moved : ∀ k, subspaceCommutator (imageRepresentation M V hn) ⊤
    ((marking k).kernel.map (c.ambientFactor d k).embedding.groupMap) =
      (c.ambientFactor d k).space
  kernel_fixed : ∀ k k', k ≠ k' →
    fixedSpace (imageRepresentation M V hn)
      ((marking k).kernel.map (c.ambientFactor d k).embedding.groupMap) =
        (c.ambientFactor d k').space
  stabilizer_index :
    ((T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d first).space : Set G)).relIndex
      (T : Subgroup G) = 2
  stabilizer_normal :
    (((T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d first).space : Set G)).subgroupOf
      (T : Subgroup G)).Normal
  stabilizes_second :
    (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d first).space : Set G) ≤
      normalizer (plane V (c.ambientFactor d second).space : Set G)
  exchanges : ∀ x ∈ (T : Subgroup G),
    x ∉ normalizer (plane V (c.ambientFactor d first).space : Set G) →
    (plane V (c.ambientFactor d first).space).map (MulAut.conj x).toMonoidHom =
      plane V (c.ambientFactor d second).space ∧
    (plane V (c.ambientFactor d second).space).map (MulAut.conj x).toMonoidHom =
      plane V (c.ambientFactor d first).space

/-- Construct the support geometry directly from the classified decomposable
action. Both odd primes remain possible, with the same prime in every marking. -/
theorem supportPair_of_decomposable {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V hn) = 2) :
    Nonempty (SupportPair (T := T) hn c d) := by
  classical
  obtain ⟨_,p,hp,hm,hd⟩ := hdec.ratio_two_dimensions hq
  choose l hl using hm
  obtain ⟨_,_,_,_,_,i,j,hij,hall,_,_,_,hcompl,t,ht,htij,_⟩ := hdec
  obtain ⟨hindex,hnormal,hsecond,hexchange⟩ := support_exchange hTM hn c d π hs i j hij hall t ht htij
  refine ⟨{
    first := i
    second := j
    distinct := hij
    covers := hall
    prime := p
    prime_cases := hp
    marking := l
    dihedral := hl
    support_card := ?_
    marked_card := ?_
    complement := (plane_complements hcompl).1
    disjoint := (plane_complements hcompl).2
    kernel_card := ?_
    kernel_moved := fun k => embedded_kernel_moved (c.ambientFactor d k) (l k)
    kernel_fixed := ?_
    stabilizer_index := hindex
    stabilizer_normal := hnormal
    stabilizes_second := hsecond
    exchanges := fun x hx hn => hexchange x hx (fun h => hn h.2) }⟩
  · intro k
    rw [plane_card,(hd k).2]
    norm_num
  · intro k
    exact (embedded_marked_four hn (c.ambientFactor d k) (l k) hq (hd k).1).1
  · intro k
    exact (card_map_of_injective (K := (l k).kernel)
      (c.ambientFactor d k).embedding.group_injective).trans (hl k).card_kernel
  · intro k k' hkk'
    apply embedded_kernel_fixed (c.ambientFactor d k) (l k) _ (c.ambient_cross d hkk'.symm)
    rcases hall k with rfl | rfl <;> rcases hall k' with rfl | rfl
    · exact False.elim (hkk' rfl)
    · exact hcompl.symm
    · exact hcompl
    · exact False.elim (hkk' rfl)

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
