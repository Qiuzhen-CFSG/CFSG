module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Planes
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import Theory.GroupTheory.SylowSubnormalIntersection
/-!
# The two original Thompson markings in the decomposable action

The Sylow intersection with the two commuting dihedral factors is the
product of its order-two intersections with those factors. Cubic ratio two
forces each involution to fix a two-dimensional subspace of its support.
The earlier source Thompson-image theorem therefore gives two actual
four-subgroups Z_i = V_i ∩ C_V(J₁(T)), splitting the whole Thompson fixed
subgroup. The original Sylow elements exchanging supports exchange these
same marked subgroups.

`ThompsonPair` retains the original supports of order sixteen, their odd
kernels and their common prime three or five. The support stabilizer
normalizes both markings and contains C_T(Z₁). Identification of the
centralizer residual and the remaining pre-exclusion marker fields are
subsequent source obligations.

Source: Aschbacher--Smith 15.1.13(4) and 15.1.16(a), printed pp.1091--1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06

private theorem sylow_card_two {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) {p : ℕ} (hp : Odd p) (hc : Nat.card D = 2*p) : Nat.card S = 2 := by
  have hd : 2 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) (by simp [hc])
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) p := by
    rw [hk]
    exact hp.coprime_two_left.pow_left k
  have hb : Nat.card S ∣ 2 := hcop.dvd_of_dvd_mul_right (hc ▸ card_subgroup_dvd_card _)
  exact Nat.dvd_antisymm hb hd

/-- The actual Sylow intersections with two commuting dihedral factors
are order two and generate the entire Sylow intersection with their product. -/
private theorem sylow_pair {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) (L R : Subgroup D) {p : ℕ} (hp : Odd p)
    (hcL : Nat.card L = 2*p) (hcR : Nat.card R = 2*p)
    (hd : Disjoint L R) (hcom : ∀ l ∈ L, ∀ r ∈ R, Commute l r)
    (hn : (L ⊔ R).Normal) :
    Nat.card ((S : Subgroup D) ⊓ L : Subgroup D) = 2 ∧
    Nat.card ((S : Subgroup D) ⊓ R : Subgroup D) = 2 ∧
    (S : Subgroup D) ⊓ (L ⊔ R) =
      ((S : Subgroup D) ⊓ L) ⊔ ((S : Subgroup D) ⊓ R) := by
  have hRL : R ≤ normalizer (L : Set D) := by
    apply le_normalizer_iff.mpr
    intro r hr l hl
    rw [(hcom l hl r hr).symm.eq,mul_inv_cancel_right]
    exact hl
  have hLR : L ≤ normalizer (R : Set D) := by
    apply le_normalizer_iff.mpr
    intro l hl r hr
    rw [(hcom l hl r hr).eq,mul_inv_cancel_right]
    exact hr
  have hLN : (L.subgroupOf (L ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hRL)
  have hRN : (R.subgroupOf (L ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hLR R.le_normalizer)
  have hLs := Subgroup.IsSubnormal.trans le_sup_left hLN.isSubnormal hn.isSubnormal
  have hRs := Subgroup.IsSubnormal.trans le_sup_right hRN.isSubnormal hn.isSubnormal
  obtain ⟨SL,hSL⟩ := S.exists_subgroupOf_eq_of_subnormal L hLs
  obtain ⟨SR,hSR⟩ := S.exists_subgroupOf_eq_of_subnormal R hRs
  have hSLc : Nat.card ((S : Subgroup D) ⊓ L : Subgroup D) = 2 := by
    have hh := sylow_card_two SL hp hcL
    rw [hSL] at hh
    rw [←map_subgroupOf_eq_of_le (show (S : Subgroup D) ⊓ L ≤ L from inf_le_right)]
    simpa only [inf_subgroupOf_right, card_map_of_injective L.subtype_injective] using hh
  have hSRc : Nat.card ((S : Subgroup D) ⊓ R : Subgroup D) = 2 := by
    have hh := sylow_card_two SR hp hcR
    rw [hSR] at hh
    rw [←map_subgroupOf_eq_of_le (show (S : Subgroup D) ⊓ R ≤ R from inf_le_right)]
    simpa only [inf_subgroupOf_right, card_map_of_injective R.subtype_injective] using hh
  have hA : Nat.card (((S : Subgroup D) ⊓ L) ⊔ ((S : Subgroup D) ⊓ R) : Subgroup D) = 4 := by
    have hn' : (S : Subgroup D) ⊓ R ≤ normalizer ((S : Subgroup D) ⊓ L : Set D) := by
      exact le_normalizer_inf (inf_le_left.trans (S : Subgroup D).le_normalizer)
        (inf_le_right.trans hRL)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn'
      (hd.mono inf_le_right inf_le_right),hSLc,hSRc]
  have hb : Nat.card ((S : Subgroup D) ⊓ (L ⊔ R) : Subgroup D) ≤ 4 := by
    apply two_group_card_le_four_of_odd_factor _ _ S.isPGroup'.to_inf_left inf_le_right
      (p*p) (hp.mul hp)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hRL hd,hcL,hcR]
    ring
  exact ⟨hSLc,hSRc,(eq_of_le_of_card_ge
    (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
    (by rw [hA]; exact hb)).symm⟩

/-- Any involution on a four-dimensional ratio-two factor fixes a plane. -/
private theorem involution_fixed_dimension {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (t : D) (ht : orderOf t = 2)
    (hq : cubicRatio ρ = 2) (hd : Module.finrank (ZMod 2) W = 4) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 2 := by
  obtain ⟨he,hr,hquad,hhalf⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  have hlo : cubicRatio ρ ≤ actionRatio ρ (zpowers t) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he,isCubic_of_isQuadratic hquad⟩ le_rfl)
  rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hlo
  have hlo' : 2 ≤ fixedCodim ρ (zpowers t) := by exact_mod_cast hlo
  have hsum := fixedCodim_add_finrank ρ (zpowers t)
  omega


private theorem fixedSpace_sup_eq {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A B : Subgroup D) :
    fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B := by
  apply le_antisymm (le_inf (fixedSpace_antitone ρ le_sup_left)
    (fixedSpace_antitone ρ le_sup_right))
  have ha : A ≤ subspaceKernel ρ (fixedSpace ρ A ⊓ fixedSpace ρ B) ⊤ :=
    fun a ha => ⟨trivial,fun v hv => hv.1 ⟨a,ha⟩⟩
  have hb : B ≤ subspaceKernel ρ (fixedSpace ρ A ⊓ fixedSpace ρ B) ⊤ :=
    fun b hb => ⟨trivial,fun v hv => hv.2 ⟨b,hb⟩⟩
  exact fun v hv a => ((sup_le ha hb) a.property).2 v hv

/-- An order-two subgroup in the literal factor fixes a two-dimensional
subspace of its support. The subgroup need not be the initial marked involution. -/
private theorem factor_involution_fixed_dimension {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ) (B : Subgroup D)
    (hBF : B ≤ F.actor) (hB : Nat.card B = 2)
    (hq : cubicRatio ρ = 2) (hd : Module.finrank (ZMod 2) F.Space = 4) :
    Module.finrank (ZMod 2) (F.space ⊓ fixedSpace ρ B : Submodule (ZMod 2) W) = 2 := by
  let A := B.comap F.embedding.groupMap
  have hmap : A.map F.embedding.groupMap = B := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hBF
  have hA : Nat.card A = 2 := by
    rw [←card_map_of_injective F.embedding.group_injective,hmap,hB]
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hto : orderOf t = 2 := by rw [←Nat.card_zpowers,ht,hA]
  have hdim : Module.finrank (ZMod 2) (fixedSpace F.action A) = 2 := by
    rw [←ht]
    exact involution_fixed_dimension F.action t hto (F.embedding.ratio.trans hq) hd
  have he : (fixedSpace F.action A).map F.embedding.spaceMap = F.space ⊓ fixedSpace ρ B := by
    apply le_antisymm
    · apply le_inf (by rintro _ ⟨w,_,rfl⟩; exact ⟨w,rfl⟩)
      rw [←hmap]
      exact F.embedding.map_fixed _ _ le_rfl
    · rintro w ⟨⟨v,rfl⟩,hv⟩
      refine ⟨v,?_,rfl⟩
      intro a
      apply F.embedding.space_injective
      change F.embedding.spaceMap (F.action (a : F.Carrier) v) = F.embedding.spaceMap v
      rw [F.embedding.equivariant]
      exact hv ⟨F.embedding.groupMap a,a.property⟩
  rw [←he,←(Submodule.equivMapOfInjective F.embedding.spaceMap
    F.embedding.space_injective (fixedSpace F.action A)).finrank_eq,hdim]

/-- Fixed vectors split across complementary supports when each actor fixes
the opposite support. -/
private theorem fixedSpace_split {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A B : Subgroup D)
    (U V : Submodule (ZMod 2) W) (hc : IsCompl U V)
    (hAV : V ≤ fixedSpace ρ A) (hBU : U ≤ fixedSpace ρ B) :
    fixedSpace ρ (A ⊔ B) =
      (U ⊓ fixedSpace ρ (A ⊔ B)) ⊔ (V ⊓ fixedSpace ρ (A ⊔ B)) := by
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  intro w hw
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp
    (show w ∈ U ⊔ V by rw [hc.sup_eq_top]; trivial)
  rw [fixedSpace_sup_eq] at hw ⊢
  have huA : u ∈ fixedSpace ρ A := by
    intro a
    have hh := hw.1 a
    rw [map_add,hAV hv a] at hh
    exact add_right_cancel hh
  have hvB : v ∈ fixedSpace ρ B := by
    intro b
    have hh := hw.2 b
    rw [map_add,hBU hu b] at hh
    exact add_left_cancel hh
  exact Submodule.mem_sup.mpr ⟨u,⟨hu,huA,hBU hu⟩,v,⟨hv,hAV hv,hvB⟩,rfl⟩


private theorem two_factor_fixed {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (S : Sylow 2 D) (F H : Factor ρ)
    {p : ℕ} (hp : Odd p) (hcF : Nat.card F.actor = 2*p) (hcH : Nat.card H.actor = 2*p)
    (hd : Disjoint F.actor H.actor)
    (hcom : ∀ f ∈ F.actor, ∀ h ∈ H.actor, Commute f h)
    (hn : (F.actor ⊔ H.actor).Normal)
    (hcrossF : F.space ≤ fixedSpace ρ H.actor)
    (hcrossH : H.space ≤ fixedSpace ρ F.actor)
    (hcompl : IsCompl F.space H.space)
    (hq : cubicRatio ρ = 2)
    (hdF : Module.finrank (ZMod 2) F.Space = 4)
    (hdH : Module.finrank (ZMod 2) H.Space = 4) :
    let C := fixedSpace ρ ((S : Subgroup D) ⊓ (F.actor ⊔ H.actor))
    Module.finrank (ZMod 2) (F.space ⊓ C : Submodule (ZMod 2) W) = 2 ∧
    Module.finrank (ZMod 2) (H.space ⊓ C : Submodule (ZMod 2) W) = 2 ∧
    C = (F.space ⊓ C) ⊔ (H.space ⊓ C) := by
  obtain ⟨hA,hB,hpair⟩ := sylow_pair S F.actor H.actor hp hcF hcH hd hcom hn
  have hF := hcrossF.trans (fixedSpace_antitone ρ (show (S : Subgroup D) ⊓ H.actor ≤ H.actor from inf_le_right))
  have hH := hcrossH.trans (fixedSpace_antitone ρ (show (S : Subgroup D) ⊓ F.actor ≤ F.actor from inf_le_right))
  dsimp only
  rw [hpair]
  refine ⟨?_,?_,fixedSpace_split ρ _ _ F.space H.space hcompl hH hF⟩
  · have he : F.space ⊓ fixedSpace ρ (((S : Subgroup D) ⊓ F.actor) ⊔ ((S : Subgroup D) ⊓ H.actor)) =
        F.space ⊓ fixedSpace ρ ((S : Subgroup D) ⊓ F.actor) := by
      rw [fixedSpace_sup_eq]
      ext w
      exact ⟨fun hw => ⟨hw.1,hw.2.1⟩,fun hw => ⟨hw.1,hw.2,hF hw.1⟩⟩
    rw [he]
    exact factor_involution_fixed_dimension F _ inf_le_right hA hq hdF
  · have he : H.space ⊓ fixedSpace ρ (((S : Subgroup D) ⊓ F.actor) ⊔ ((S : Subgroup D) ⊓ H.actor)) =
        H.space ⊓ fixedSpace ρ ((S : Subgroup D) ⊓ H.actor) := by
      rw [fixedSpace_sup_eq]
      ext w
      exact ⟨fun hw => ⟨hw.1,hw.2.2⟩,fun hw => ⟨hw.1,hH hw.1,hw.2⟩⟩
    rw [he]
    exact factor_involution_fixed_dimension H _ inf_le_right hB hq hdH

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem plane_inf {V : Subgroup G} [IsElementaryAbelian 2 V]
    (A B : Submodule (ZMod 2) (Additive V)) :
    plane V (A ⊓ B) = plane V A ⊓ plane V B := by
  exact map_inf (binarySubgroup A) (binarySubgroup B) V.subtype V.subtype_injective

omit [Finite G] in
private theorem plane_sup {V : Subgroup G} [IsElementaryAbelian 2 V]
    (A B : Submodule (ZMod 2) (Additive V)) :
    plane V (A ⊔ B) = plane V A ⊔ plane V B := by
  apply le_antisymm
  · rintro x ⟨v,hv,rfl⟩
    change Additive.ofMul v ∈ A ⊔ B at hv
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
    have he' := congrArg (fun w : Additive V => (w.toMul : G)) he
    change (a.toMul : G) * b.toMul = (v : G) at he'
    change (v : G) ∈ plane V A ⊔ plane V B
    rw [←he']
    exact (plane V A ⊔ plane V B).mul_mem
      (mem_sup_left (mem_map_of_mem V.subtype ha))
      (mem_sup_right (mem_map_of_mem V.subtype hb))
  · apply sup_le
    · apply map_mono
      intro x hx
      exact (show A ≤ A ⊔ B from le_sup_left) hx
    · apply map_mono
      intro x hx
      exact (show B ≤ A ⊔ B from le_sup_right) hx

/-- The fixed subspace of the actual Thompson image is the literal V_E. -/
theorem plane_thompson_image {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G)) :
    plane V (fixedSpace (imageRepresentation M V hn)
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)) = thompsonFixed T V := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨v.property,?_⟩
    intro j hj
    have hJ := hTM (ChapterB.thompsonJ_le _ _ hj)
    have he := congrArg (fun w : Additive V => (w.toMul : G))
      (hv ⟨(actionHom M V hn).rangeRestrict ⟨j,hJ⟩,mem_map_of_mem _ hj⟩)
    exact mul_inv_eq_iff_eq_mul.mp he
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    rintro ⟨_,j,hj,rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (j : G) * x * (j : G)⁻¹ = x
    rw [hc j hj,mul_inv_cancel_right]

/-- The original four-element marking in a support, using J₁(T). -/
@[expose] def thompsonPlane (T : Sylow 2 G) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  plane V W ⊓ thompsonFixed T V

/-- Both source Thompson markings have order four and split V_E. The input
is the proved earlier Thompson-image equality, with the same factor action. -/
theorem thompson_planes_of_image {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V hn) = 2)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    (∀ k, Nat.card (thompsonPlane T V (c.ambientFactor d k).space) = 4) ∧
    ∀ i j : d.Index, i ≠ j →
      thompsonFixed T V = thompsonPlane T V (c.ambientFactor d i).space ⊔
        thompsonPlane T V (c.ambientFactor d j).space := by
  let ρ := imageRepresentation M V hn
  let S : Sylow 2 (internalActionImage M V hn) :=
    (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let C := fixedSpace ρ ((S : Subgroup (internalActionImage M V hn)) ⊓ Jhat ρ)
  have hc : plane V C = thompsonFixed T V := by
    exact (congrArg (fun A : Subgroup (internalActionImage M V hn) =>
      plane V (fixedSpace ρ A)) hJ.symm).trans (plane_thompson_image hTM hn)
  obtain ⟨_,_,_,_,hdim⟩ := hdec.ratio_two_dimensions hq
  obtain ⟨_,p,m,hpm,hmark,i,j,hij,hall,hgen,hdis,hcom,hcompl,_⟩ := hdec
  have hp : Odd p := by
    rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have hcard (k : d.Index) : Nat.card (c.ambientFactor d k).actor = 2*p := by
    obtain ⟨l,hl⟩ := hmark k
    exact (Nat.card_range_of_injective (c.ambientFactor d k).embedding.group_injective).trans
      ((Nat.card_congr hl.dihedral.some.toEquiv).trans DihedralGroup.nat_card)
  have hnormal : ((c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor).Normal := by
    rw [hgen]
    exact Jhat_normal ρ
  obtain ⟨hi,hj,hsplit⟩ := two_factor_fixed S (c.ambientFactor d i) (c.ambientFactor d j)
    hp (hcard i) (hcard j) hdis hcom hnormal
    (c.ambient_cross d hij) (c.ambient_cross d hij.symm) hcompl hq (hdim i).1 (hdim j).1
  rw [hgen] at hi hj hsplit
  have hdimC (k : d.Index) : Module.finrank (ZMod 2)
      ((c.ambientFactor d k).space ⊓ C : Submodule (ZMod 2) (Additive V)) = 2 := by
    rcases hall k with rfl | rfl
    · exact hi
    · exact hj
  have hplane (k : d.Index) :
      plane V ((c.ambientFactor d k).space ⊓ C) =
        thompsonPlane T V (c.ambientFactor d k).space := by
    rw [plane_inf,hc]
    rfl
  constructor
  · intro k
    rw [←hplane,plane_card,hdimC]
    norm_num
  · intro a b hab
    have he : thompsonFixed T V = thompsonPlane T V (c.ambientFactor d i).space ⊔
        thompsonPlane T V (c.ambientFactor d j).space := by
      have he := congrArg (plane V) hsplit
      change plane V C = plane V ((c.ambientFactor d i).space ⊓ C ⊔
        (c.ambientFactor d j).space ⊓ C) at he
      rw [plane_sup,hplane,hplane] at he
      exact hc.symm.trans he
    rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl
    · exact False.elim (hab rfl)
    · exact he
    · exact he.trans (sup_comm _ _)
    · exact False.elim (hab rfl)


/-- Support geometry with the actual Thompson markings. Both the original
prime and odd kernels are inherited from the same `SupportPair`. -/
structure ThompsonPair {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) extends SupportPair (T := T) hn c d where
  thompson_card : ∀ k, Nat.card (thompsonPlane T V (c.ambientFactor d k).space) = 4
  thompson_split : thompsonFixed T V =
    thompsonPlane T V (c.ambientFactor d first).space ⊔
      thompsonPlane T V (c.ambientFactor d second).space
  thompson_disjoint : thompsonPlane T V (c.ambientFactor d first).space ⊓
    thompsonPlane T V (c.ambientFactor d second).space = ⊥
  thompson_normalized :
    (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d first).space : Set G) ≤
      normalizer (thompsonPlane T V (c.ambientFactor d first).space : Set G) ⊓
        normalizer (thompsonPlane T V (c.ambientFactor d second).space : Set G)
  thompson_exchanges : ∀ x ∈ (T : Subgroup G),
    x ∉ normalizer (plane V (c.ambientFactor d first).space : Set G) →
    (thompsonPlane T V (c.ambientFactor d first).space).map (MulAut.conj x).toMonoidHom =
      thompsonPlane T V (c.ambientFactor d second).space ∧
    (thompsonPlane T V (c.ambientFactor d second).space).map (MulAut.conj x).toMonoidHom =
      thompsonPlane T V (c.ambientFactor d first).space
  centralizer_le_stabilizer :
    (T : Subgroup G) ⊓ centralizer (thompsonPlane T V (c.ambientFactor d first).space : Set G) ≤
      normalizer (plane V (c.ambientFactor d first).space : Set G)

/-- Construct and exchange the two genuine Thompson markings. The earlier
15.1.13 image equality is the only additional premise in this transport step. -/
theorem thompsonPair_of_image {T : Sylow 2 G} {M V : Subgroup G}
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
    (hq : cubicRatio (imageRepresentation M V hn) = 2)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    Nonempty (ThompsonPair (T := T) hn c d) := by
  obtain ⟨s⟩ := supportPair_of_decomposable hTM hn c d π hs hdec hq
  obtain ⟨hcard,hsplit⟩ := thompson_planes_of_image hTM hn c d π hdec hq hJ
  have hnorm : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    le_normalizer_inf (hTM.trans hn) ((ChapterB.le_normalizer_thompsonJ _ _).trans
      (normalizer_le_normalizer_centralizer _))
  have hexchange (x : G) (hx : x ∈ (T : Subgroup G))
      (hout : x ∉ normalizer (plane V (c.ambientFactor d s.first).space : Set G)) :
      (thompsonPlane T V (c.ambientFactor d s.first).space).map (MulAut.conj x).toMonoidHom =
        thompsonPlane T V (c.ambientFactor d s.second).space ∧
      (thompsonPlane T V (c.ambientFactor d s.second).space).map (MulAut.conj x).toMonoidHom =
        thompsonPlane T V (c.ambientFactor d s.first).space := by
    obtain ⟨h1,h2⟩ := s.exchanges x hx hout
    have he := mem_normalizer_iff_map_conj_eq.mp (hnorm hx)
    change (thompsonFixed T V).map (MulAut.conj x).toMonoidHom = thompsonFixed T V at he
    constructor <;> dsimp only [thompsonPlane] <;>
      rw [map_inf _ _ _ (MulAut.conj x).injective,he]
    · rw [h1]
    · rw [h2]
  have hdis : thompsonPlane T V (c.ambientFactor d s.first).space ⊓
      thompsonPlane T V (c.ambientFactor d s.second).space = ⊥ := by
    apply bot_unique
    exact (inf_le_inf inf_le_left inf_le_left).trans s.disjoint.le
  refine ⟨{ toSupportPair := s
            thompson_card := hcard
            thompson_split := hsplit s.first s.second s.distinct
            thompson_disjoint := hdis
            thompson_normalized := ?_
            thompson_exchanges := hexchange
            centralizer_le_stabilizer := ?_ }⟩
  · exact le_inf (le_normalizer_inf inf_le_right (inf_le_left.trans hnorm))
      (le_normalizer_inf s.stabilizes_second (inf_le_left.trans hnorm))
  · intro x hx
    by_contra hout
    have he := (mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hx.2)).symm.trans
      (hexchange x hx.1 hout).1
    have hb : thompsonPlane T V (c.ambientFactor d s.first).space = ⊥ := by
      rw [←he,inf_idem] at hdis
      exact hdis
    have hc := hcard s.first
    rw [hb,card_bot] at hc
    omega

/-- The original prepared decomposable action supplies the Thompson equality
and hence constructs its two marked four-groups, with no marking callback. -/
theorem thompsonPair_of_decomposable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized) (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
      (actionHom M V h.normalized).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V h.normalized) = 2) :
    Nonempty (ThompsonPair (T := T) h.normalized c d) := by
  subst V
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq (fun E hE => hE.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  exact thompsonPair_of_image hM.1.2 h.normalized c d π hs hdec hq he

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
