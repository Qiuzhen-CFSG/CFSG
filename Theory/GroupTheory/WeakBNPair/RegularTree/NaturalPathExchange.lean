module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Natural-module cubic exchange on actual apartment paths

The local quotient map is defined on a subgroup of the midpoint stabilizer.
Its kernel is exactly the original vertex two-core, with an equivariant
isomorphism to the natural plane. Both half-path radicals carry the opposite
root markings. A reversing local actor interchanges them, forcing its
quotient matrix to be anti-diagonal. The cubic calculation constructs the
opposite element, proves the cubic relation upstairs and kills the common
centralizer. The diagonal ratio places the correction in the original core
times Cartan, so the half-path factorization proves exchange.

The final transport lemma conjugates the resulting exchange actor along an
alignment of two actual paths. The source application needs coordinates on
only two constructed paths, one for each original vertex orbit. This module
does not construct the preceding local profiles or select the reflections.

Source: DGS, *Groups and Graphs* (1985), (14.12)--(14.13), pp.217--218.
-/

@[expose] public noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open NaturalCubic
universe u v w
variable {X : Type v} {V : Type w} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {a b : V}

/-- Local quotient and natural-module coordinates inside the literal midpoint
stabilizer, with both half-path roots and the same apartment Cartan marked. -/
structure NaturalPathCoordinates (p : Γ.Walk a b) (n : ℕ) (K : Subgroup X) where
  F : Type u
  [field : Field F]
  [charTwo : CharP F 2]
  localGroup : Subgroup X
  local_le : localGroup ≤ MulAction.stabilizer X (p.getVert n)
  core_le : (MulAction.stabilizer X (p.getVert n)).pCoreIn 2 ≤ localGroup
  upper_le : pathRoot (X := X) (p.drop n) ≤ localGroup
  lower_le : pathRoot (X := X) (p.take n) ≤ localGroup
  quotient : localGroup →* SL(2,F)
  kernel_eq : quotient.ker =
    ((MulAction.stabilizer X (p.getVert n)).pCoreIn 2).subgroupOf
      localGroup
  natural : NaturalKernel quotient
  upper_image : ∀ x : localGroup,
    (x:X)∈pathRoot (X := X) (p.drop n) → ∃ a : F, quotient x=upper a
  lower_elements : ∀ y : localGroup,
    (y:X)∈pathRoot (X := X) (p.take n) → ∃ a : F, quotient y=lower a
  lower_image : ∀ a : F, ∃ y : localGroup,
    (y:X)∈pathRoot (X := X) (p.take n) ∧ quotient y=lower a
  diagonal_image : ∀ a : F, ∀ ha : a≠0,
    diag2 a ha∈(K.subgroupOf localGroup).map quotient
  reflection : localGroup
  reverses : ∀ k≤2*n, (reflection:X) • p.getVert k=p.getVert (2*n-k)

attribute [instance] NaturalPathCoordinates.field NaturalPathCoordinates.charTwo

namespace NaturalPathCoordinates
variable {p : Γ.Walk a b} {n : ℕ} {K : Subgroup X}
variable (d : NaturalPathCoordinates.{u} p n K)

include d in
/-- Actual natural coordinates construct each opposite cubic pair, including
its reflection correction and its trivial common centralizer in O₂(P). -/
theorem exists_pair (hlen : p.length=2*n)
    (hSQ : pathRoot (X := X) (p.take n) ⊓
      (MulAction.stabilizer X (p.getVert n)).pCoreIn 2=⊥)
    (x : X) (hx : x∈pathRoot (X := X) (p.drop n)) (hne : x≠1) :
    ∃ y∈pathRoot (X := X) (p.take n), ∃ t : X,
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      (∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) ∧
      (x*y*x)*t⁻¹∈(MulAction.stabilizer X (p.getVert n)).pCoreIn 2 ⊔ K ∧
      ∀ z∈(MulAction.stabilizer X (p.getVert n)).pCoreIn 2,
        Commute x z → Commute y z → z=1 := by
  let P := MulAction.stabilizer X (p.getVert n)
  let Q := P.pCoreIn 2
  let A := d.localGroup
  let R := (pathRoot (X := X) (p.drop n)).subgroupOf A
  let S := (pathRoot (X := X) (p.take n)).subgroupOf A
  have hRQ := reflected_root_disjoint p n hlen Q hSQ (vertexCore_normalized _)
    d.reflection d.reverses
  have hr : R ⊓ d.quotient.ker=⊥ := by
    rw [d.kernel_eq]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hm : (z:X)∈pathRoot (X := X) (p.drop n) ⊓ Q := ⟨hz.1,hz.2⟩
    rwa [hRQ] at hm
  have hs : S ⊓ d.quotient.ker=⊥ := by
    rw [d.kernel_eq]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hm : (z:X)∈pathRoot (X := X) (p.take n) ⊓ Q := ⟨hz.1,hz.2⟩
    rwa [hSQ] at hm
  have hxA : x∈A := d.upper_le hx
  obtain ⟨a,ha,hπx,y,hy,hπy,hxx,hyy,horder,hcentral⟩ :=
    pair_of_opposite_images d.quotient d.natural R S hr hs d.upper_image
      d.lower_image ⟨x,hxA⟩ hx (fun he => hne (congrArg Subtype.val he))
  have hhalves := pathRoot_halves_reflection p n hlen (d.reflection:X) d.reverses
  let xx : A := ⟨x,hxA⟩
  have hxS : ((d.reflection*xx*d.reflection⁻¹ : A):X)∈pathRoot (X := X) (p.take n) := by
    rw [← hhalves.2]
    exact ⟨x,hx,rfl⟩
  have hyR : ((d.reflection*y*d.reflection⁻¹ : A):X)∈pathRoot (X := X) (p.drop n) := by
    rw [← hhalves.1]
    exact ⟨y,hy,rfl⟩
  obtain ⟨b,hb⟩ := d.lower_elements (d.reflection*xx*d.reflection⁻¹) hxS
  obtain ⟨e,he⟩ := d.upper_image (d.reflection*y*d.reflection⁻¹) hyR
  have hxπ : d.quotient xx=upper a := hπx
  have hux : d.quotient d.reflection*upper a=lower b*d.quotient d.reflection := by
    calc
      _ = d.quotient (d.reflection*xx*d.reflection⁻¹)*d.quotient d.reflection := by
        simp only [map_mul,map_inv,hxπ,mul_assoc,inv_mul_cancel,mul_one]
      _ = _ := by rw [hb]
  have hly : d.quotient d.reflection*lower a⁻¹=upper e*d.quotient d.reflection := by
    calc
      _ = d.quotient (d.reflection*y*d.reflection⁻¹)*d.quotient d.reflection := by
        simp only [map_mul,map_inv,hπy,mul_assoc,inv_mul_cancel,mul_one]
      _ = _ := by rw [he]
  obtain ⟨c,hc,hπt⟩ := braid_of_intertwines (d.quotient d.reflection) a b a⁻¹ e
    ha (inv_ne_zero ha) hux hly
  have hcor := correction_mem d.quotient (K.subgroupOf A) a c ha hc
    ⟨x,hxA⟩ y d.reflection hπx hπy hπt d.diagonal_image
  have hcorX : (x*(y:X)*x)*(d.reflection:X)⁻¹∈Q ⊔ K := by
    have hm := Subgroup.mem_map_of_mem A.subtype hcor
    rw [Subgroup.map_sup,d.kernel_eq,
      Subgroup.map_subgroupOf_eq_of_le d.core_le] at hm
    exact (sup_le_sup_left (show (K.subgroupOf A).map A.subtype ≤ K by
      rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left) Q) hm
  refine ⟨y,hy,d.reflection,congrArg Subtype.val hxx,congrArg Subtype.val hyy,?_,
    d.reverses,hcorX,?_⟩
  · exact (orderOf_injective A.subtype Subtype.coe_injective (⟨x,hxA⟩*y)).trans horder
  · intro z hz hxz hyz
    have hzP : z∈A := d.core_le hz
    have hzker : (⟨z,hzP⟩ : A)∈d.quotient.ker := by rw [d.kernel_eq]; exact hz
    have hxzP : Commute (⟨x,hxA⟩ : A) ⟨z,hzP⟩ := by
      apply Subtype.ext
      exact hxz.eq
    have hyzP : Commute y (⟨z,hzP⟩ : A) := by
      apply Subtype.ext
      exact hyz.eq
    exact congrArg Subtype.val (hcentral ⟨z,hzP⟩ hzker hxzP hyzP)

end NaturalPathCoordinates

/-- Factor the arbitrary half-path fixer and apply the constructed natural
cubic pair. No pair-existence or centralizer-bound callback remains. -/
theorem halfFixer_exchange_of_natural_coordinates
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length=2*n) (K : Subgroup X)
    (hK : K ≤ pathFixer (X := X) p)
    (hfactor : (pathFixer (X := X) (p.drop n) : Set X)=
      (pathRoot (X := X) (p.drop n) : Set X)*(K : Set X))
    (hSQ : pathRoot (X := X) (p.take n) ⊓
      (MulAction.stabilizer X (p.getVert n)).pCoreIn 2=⊥)
    (d : NaturalPathCoordinates.{u} p n K)
    (g : X) (hg : ∀ k, n≤k → k≤2*n → g • p.getVert k=p.getVert k)
    (hmove : g • a≠a) :
    ∃ z : X, (∀ k≤n, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b := by
  let Q := (MulAction.stabilizer X (p.getVert n)).pCoreIn 2
  have hgF : g∈(pathFixer (X := X) (p.drop n) : Set X) := by
    intro k hk
    rw [SimpleGraph.Walk.drop_length,hlen] at hk
    rw [SimpleGraph.Walk.drop_getVert]
    exact hg (n+k) (by omega) (by omega)
  rw [hfactor] at hgF
  obtain ⟨x,hx,k,hk,rfl⟩ := hgF
  have hka : k • a=a := by
    simpa only [SimpleGraph.Walk.getVert_zero] using hK hk 0 (Nat.zero_le _)
  have he : (x*k) • a=x • a := by rw [mul_smul,hka]
  have hxne : x≠1 := by intro hh; rw [he,hh,one_smul] at hmove; exact hmove rfl
  obtain ⟨y,hy,u,hxx,hyy,horder,hu,hcor,hcentral⟩ := d.exists_pair hlen hSQ x hx hxne
  obtain ⟨k,_,ht,hQt⟩ := correct_path_reflection p n hlen K Q hK
    (vertexCore_normalized _) (x*y*x) u hu hcor
  have hxn : x∈Subgroup.normalizer (Q : Set X) := by
    apply vertexCore_normalized (p.getVert n)
    change x • p.getVert n=p.getVert n
    have hh := (Subgroup.pCoreIn_le 2 _ hx) 0 (Nat.zero_le _)
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hyn : y∈Subgroup.normalizer (Q : Set X) :=
    vertexCore_normalized _ (pathRoot_fixes (p.take n) hy).1
  have hRQ := reflected_root_disjoint p n hlen Q hSQ (vertexCore_normalized _) (k*u) ht
  rcases path_braid_exchange_or_centralizer p n hlen Q hRQ hSQ hx hy hxn hyn hxx hyy
      (by rw [← horder]; exact pow_orderOf_eq_one _) ht hQt with hex | ⟨z,hz,hzne,hxz,hyz⟩
  · simpa only [he] using hex
  · exact (hzne (hcentral z hz hxz hyz)).elim

/-- Aligning the vertices of two paths transports the literal exchange
actor, including its fixation of the first half and its endpoint equation. -/
theorem exchange_along_path_map {c e : V}
    (p : Γ.Walk a b) (q : Γ.Walk c e) (n : ℕ) (hp : p.length=2*n)
    (f : X) (hf : ∀ k≤2*n, f • p.getVert k=q.getVert k)
    (hq : q.length=2*n)
    (hex : ∀ g : X,
      (∀ k, n≤k → k≤2*n → g • p.getVert k=p.getVert k) → g • a≠a →
      ∃ z : X, (∀ k≤n, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b)
    (g : X) (hg : ∀ k, n≤k → k≤2*n → g • q.getVert k=q.getVert k)
    (hmove : g • c≠c) :
    ∃ z : X, (∀ k≤n, z • q.getVert k=q.getVert k) ∧ z • (g • c)=e := by
  have hfa : f • a=c := by simpa only [SimpleGraph.Walk.getVert_zero] using hf 0 (by omega)
  have hfb : f • b=e := by
    have hpb : p.getVert (2*n)=b := by rw [← hp,SimpleGraph.Walk.getVert_length]
    have hqe : q.getVert (2*n)=e := by rw [← hq,SimpleGraph.Walk.getVert_length]
    simpa only [hpb,hqe] using hf (2*n) le_rfl
  let g₀ := f⁻¹*g*f
  have hg₀ : ∀ k, n≤k → k≤2*n → g₀ • p.getVert k=p.getVert k := by
    intro k hk hk'
    change (f⁻¹*g*f) • p.getVert k=p.getVert k
    rw [mul_smul,mul_smul,hf k hk',hg k hk hk',← hf k hk',inv_smul_smul]
  have hmove₀ : g₀ • a≠a := by
    intro he
    apply hmove
    calc
      g • c = f • (g₀ • a) := by simp [g₀,mul_smul,hfa]
      _ = f • a := by rw [he]
      _ = c := hfa
  obtain ⟨z,hz,hze⟩ := hex g₀ hg₀ hmove₀
  refine ⟨f*z*f⁻¹,?_,?_⟩
  · intro k hk
    rw [← hf k (by omega),mul_smul,mul_smul,inv_smul_smul,hz k hk]
  · calc
      (f*z*f⁻¹) • (g • c) = f • (z • (g₀ • a)) := by simp [g₀,mul_smul,hfa]
      _ = e := by rw [hze,hfb]

end Theory.GroupTheory.WeakBNPair.RegularTree
