module
public import Theory.GroupTheory.WeakBNPair.RegularTree.BraidCorrection
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootRegularity
public import Theory.GroupTheory.SylowKernelCore

/-!
# Cubic root pairs on actual half paths

Transport pointwise path fixers and their two-cores under a reversing
apartment reflection. Odd length-(n+1) path fixers make a half-path radical
disjoint from the midpoint two-core, provided that core fixes the neighbors.
The cubic rank-one calculation then gives exchange or a concrete nontrivial
common centralizer in that same two-core. Factoring a half-path fixer as
its radical times the apartment Cartan extends the result to every actor
in the source exchange condition. The Cartan part of a reflection correction
is absorbed into the reversing actor, so the pair input only needs its
correction in the product of the midpoint core and the Cartan.

The final inference assumes the actual order-three pair and reflection-coset
identities and a common-centralizer bound. It does not assume exchange or
any finite recognition conclusion. The two-core is never identified with
the full local permutation kernel.

Source: DGS, *Groups and Graphs* (1985), Part II, (14.1), (14.12),
printed pp.210,217--218; the exchange convention of (3.6), pp.77--78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open scoped Pointwise
open SimpleGraph SimpleGraph.Walk
variable {X V : Type*} [Group X] [MulAction X V]


/-- A path fixer fixes exactly its support. -/
theorem mem_pathFixer_support {Γ : SimpleGraph V} {a b : V} (p : Γ.Walk a b) (x : X) :
    x ∈ pathFixer (X := X) p ↔ ∀ z∈p.support, x • z=z := by
  constructor
  · intro hx z hz
    obtain ⟨k, rfl, hk⟩ := mem_support_iff_exists_getVert.mp hz
    exact hx k hk
  · intro hx k _
    exact hx _ (p.getVert_mem_support k)

/-- Reversing a path preserves its pointwise fixer. -/
theorem pathFixer_reverse {Γ : SimpleGraph V} {a b : V} (p : Γ.Walk a b) :
    pathFixer (X := X) p.reverse = pathFixer p := by
  ext x
  simp only [mem_pathFixer_support, support_reverse, List.mem_reverse]

/-- Reversing a path preserves its actual two-core. -/
theorem pathRoot_reverse {Γ : SimpleGraph V} {a b : V} (p : Γ.Walk a b) :
    pathRoot (X := X) p.reverse = pathRoot p := by
  unfold pathRoot
  rw [pathFixer_reverse]

/-- An actor matching the vertices of two paths conjugates their pointwise fixers. -/
theorem pathFixer_map_conj {Γ : SimpleGraph V} {a b c d : V}
    (p : Γ.Walk a b) (q : Γ.Walk c d) (t : X)
    (hlen : p.length=q.length)
    (ht : ∀ k≤p.length, t • p.getVert k=q.getVert k) :
    (pathFixer (X := X) p).map (MulAut.conj t).toMonoidHom = pathFixer q := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩ k hk
    change (t*u*t⁻¹) • q.getVert k=q.getVert k
    rw [← ht k (by omega), mul_smul, mul_smul, inv_smul_smul,
      hu k (by omega)]
  · intro hx
    refine ⟨t⁻¹*x*t, ?_, ?_⟩
    · intro k hk
      rw [mul_smul, mul_smul, ht k hk, hx k (by omega), ← ht k hk,
        inv_smul_smul]
    · change t*(t⁻¹*x*t)*t⁻¹=x
      group

/-- The same actor transports the actual path radicals. -/
theorem pathRoot_map_conj {Γ : SimpleGraph V} {a b c d : V}
    (p : Γ.Walk a b) (q : Γ.Walk c d) (t : X)
    (hlen : p.length=q.length)
    (ht : ∀ k≤p.length, t • p.getVert k=q.getVert k) :
    (pathRoot (X := X) p).map (MulAut.conj t).toMonoidHom = pathRoot q := by
  unfold pathRoot
  rw [Subgroup.map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective,
    pathFixer_map_conj p q t hlen ht]

/-- Reversing a centered path interchanges its two genuine half-path roots. -/
theorem pathRoot_halves_reflection {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length=2*n) (t : X)
    (ht : ∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) :
    (pathRoot (X := X) (p.take n)).map (MulAut.conj t).toMonoidHom = pathRoot (p.drop n) ∧
    (pathRoot (X := X) (p.drop n)).map (MulAut.conj t).toMonoidHom = pathRoot (p.take n) := by
  constructor
  · rw [← pathRoot_reverse (p.drop n)]
    apply pathRoot_map_conj
    · simp only [take_length, drop_length, length_reverse, hlen]
      omega
    · intro k hk
      rw [take_length, hlen] at hk
      rw [take_getVert, min_eq_right (by omega : k≤n), ht k (by omega),
        getVert_reverse, drop_length, hlen, drop_getVert]
      congr 1
      omega
  · rw [← pathRoot_reverse (p.take n)]
    apply pathRoot_map_conj
    · simp only [take_length, drop_length, length_reverse, hlen]
      omega
    · intro k hk
      rw [drop_length, hlen] at hk
      rw [drop_getVert, ht (n+k) (by omega), getVert_reverse, take_length,
        hlen, take_getVert]
      congr 1
      omega

/-- The cubic calculation on actual half-path radicals, retaining its kernel-centralizer alternative. -/
theorem path_braid_exchange_or_centralizer {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length=2*n)
    (Q : Subgroup X)
    (hRQ : pathRoot (X := X) (p.drop n) ⊓ Q=⊥)
    (hSQ : pathRoot (X := X) (p.take n) ⊓ Q=⊥)
    {x y t : X} (hxR : x∈pathRoot (X := X) (p.drop n))
    (hyS : y∈pathRoot (X := X) (p.take n))
    (hxn : x∈Subgroup.normalizer (Q : Set X))
    (hyn : y∈Subgroup.normalizer (Q : Set X))
    (hx : x*x=1) (hy : y*y=1) (hc : (x*y)^3=1)
    (ht : ∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k))
    (hQ : (x*y*x)*t⁻¹∈Q) :
    (∃ z : X, (∀ k≤n, z • p.getVert k=p.getVert k) ∧ z • (x • a)=b) ∨
      ∃ h∈Q, h≠1 ∧ Commute x h ∧ Commute y h := by
  have hr := pathRoot_halves_reflection p n hlen t ht
  have hty : t*y*t⁻¹∈pathRoot (X := X) (p.drop n) := by
    rw [← hr.1]
    exact ⟨y, hyS, rfl⟩
  have htx : t*x*t⁻¹∈pathRoot (X := X) (p.take n) := by
    rw [← hr.2]
    exact ⟨x, hxR, rfl⟩
  have htab : t • a=b := by
    simpa only [getVert_zero, Nat.sub_zero, ← hlen, getVert_length] using ht 0 (by omega)
  have hxb : x • b=b := (pathRoot_fixes (p.drop n) hxR).1
  rcases braid_exchange_or_centralizer _ _ Q hRQ hSQ hxR hyS hxn hyn hx hy
      (braid_of_involutions_cube x y hx hy hc) hty htx hQ htab hxb with he | he
  · left
    refine ⟨y, ?_, he⟩
    intro k hk
    have hh := (Subgroup.pCoreIn_le 2 _ hyS) k
      (show k≤(p.take n).length by rw [take_length, hlen]; omega)
    simpa only [take_getVert, min_eq_right hk] using hh
  · exact Or.inr he

/-- The relative vertex core is normalized by the vertex stabilizer. -/
theorem vertexCore_normalized (a : V) :
    MulAction.stabilizer X a ≤ Subgroup.normalizer
      ((MulAction.stabilizer X a).pCoreIn 2 : Set X) := by
  let P := MulAction.stabilizer X a
  have hh := (pCore 2 P).le_normalizer_map P.subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, Subgroup.pCoreIn] using hh

/-- Oddness of the next path fixer separates a half-path root from the midpoint core. -/
theorem pathRoot_take_inf_vertexCore {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (hp : p.IsPath) (n : ℕ) (hlen : n+1≤p.length)
    (hodd : ∀ {u v} (q : Γ.Walk u v), q.IsPath → q.length=n+1 →
      Odd (Nat.card (pathFixer (X := X) q)))
    (hQ : (MulAction.stabilizer X (p.getVert n)).pCoreIn 2 ≤
      MulAction.stabilizer X (p.getVert (n+1))) :
    pathRoot (X := X) (p.take n) ⊓ (MulAction.stabilizer X (p.getVert n)).pCoreIn 2=⊥ := by
  have hadj := p.adj_getVert_succ (by omega : n<p.length)
  have hnew : p.getVert (n+1) ∉ (p.take n).support := by
    intro hm
    obtain ⟨j, he, hj⟩ := mem_support_iff_exists_getVert.mp hm
    rw [take_length] at hj
    rw [take_getVert, min_eq_right (by omega : j≤n)] at he
    have hh := hp.getVert_injOn (by omega : j≤p.length) hlen he
    omega
  have ho := hodd ((p.take n).concat hadj) ((hp.take n).concat hnew hadj)
    (by rw [length_concat, take_length, min_eq_left (by omega)])
  exact le_bot_iff.mp ((inf_le_inf_left _ hQ).trans
    (pathRoot_inf_stabilizer_eq_bot (p.take n) hadj ho).le)

/-- A Cartan factor in a reflection correction can be absorbed into the reversing actor. -/
theorem correct_path_reflection {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length = 2*n) (K Q : Subgroup X)
    (hK : K ≤ pathFixer (X := X) p)
    (hQnorm : MulAction.stabilizer X (p.getVert n) ≤ Subgroup.normalizer (Q : Set X))
    (w u : X) (hu : ∀ j ≤ 2*n, u • p.getVert j = p.getVert (2*n-j))
    (hcoset : w*u⁻¹ ∈ ((Q ⊔ K : Subgroup X) : Set X)) :
    ∃ k ∈ K, (∀ j ≤ 2*n, (k*u) • p.getVert j = p.getVert (2*n-j)) ∧
      w*(k*u)⁻¹ ∈ Q := by
  have hKN : K ≤ Subgroup.normalizer (Q : Set X) := by
    intro k hk
    exact hQnorm (hK hk n (by omega))
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q K hKN] at hcoset
  obtain ⟨q, hq, k, hk, he⟩ := hcoset
  refine ⟨k, hk, ?_, ?_⟩
  · intro j hj
    rw [mul_smul, hu j hj]
    exact hK hk (2*n-j) (by omega)
  · have heq : w*(k*u)⁻¹=q := by
      calc
        _ = (w*u⁻¹)*k⁻¹ := by group
        _ = (q*k)*k⁻¹ := by rw [← he]
        _ = q := mul_inv_cancel_right q k
    rwa [heq]

/-- A midpoint reflection transports root-core disjointness to the opposite half. -/
theorem reflected_root_disjoint {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length=2*n) (Q : Subgroup X)
    (hSQ : pathRoot (X := X) (p.take n) ⊓ Q=⊥)
    (hQnorm : MulAction.stabilizer X (p.getVert n) ≤ Subgroup.normalizer (Q : Set X))
    (t : X) (ht : ∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) :
    pathRoot (X := X) (p.drop n) ⊓ Q=⊥ := by
  have htP : t∈MulAction.stabilizer X (p.getVert n) := by
    change t • p.getVert n=p.getVert n
    simpa only [show 2*n-n=n by omega] using ht n (by omega)
  apply le_bot_iff.mp
  intro x hx
  have hr := (pathRoot_halves_reflection p n hlen t ht).2
  have hm : t*x*t⁻¹∈pathRoot (X := X) (p.take n) ⊓ Q := by
    constructor
    · rw [← hr]
      exact ⟨x,hx.1,rfl⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hQnorm htP) x).mp hx.2
  rw [hSQ] at hm
  have he := congrArg (fun z : X => t⁻¹*z*t) (show t*x*t⁻¹=1 from hm)
  change x=1
  simpa only [mul_one, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] using he

/-- Reducing an arbitrary half-path fixer to its radical retains the actor's movement. -/
theorem halfFixer_exchange_or_centralizer {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length=2*n) (K Q : Subgroup X)
    (hK : K ≤ pathFixer (X := X) p)
    (hfactor : (pathFixer (X := X) (p.drop n) : Set X) =
      (pathRoot (X := X) (p.drop n) : Set X) * (K : Set X))
    (hSQ : pathRoot (X := X) (p.take n) ⊓ Q=⊥)
    (hQnorm : MulAction.stabilizer X (p.getVert n) ≤ Subgroup.normalizer (Q : Set X))
    (hpairs : ∀ x∈pathRoot (X := X) (p.drop n), x≠1 →
      ∃ y∈pathRoot (X := X) (p.take n), ∃ t : X,
        x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
        (∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) ∧ (x*y*x)*t⁻¹∈Q ⊔ K)
    (g : X) (hg : ∀ k, n≤k → k≤2*n → g • p.getVert k=p.getVert k)
    (hmove : g • a≠a) :
    (∃ z : X, (∀ k≤n, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) ∨
      ∃ x∈pathRoot (X := X) (p.drop n), ∃ y∈pathRoot (X := X) (p.take n),
        x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
        ∃ h∈Q, h≠1 ∧ Commute x h ∧ Commute y h := by
  have hgF : g∈(pathFixer (X := X) (p.drop n) : Set X) := by
    intro k hk
    rw [drop_length, hlen] at hk
    rw [drop_getVert]
    exact hg (n+k) (by omega) (by omega)
  rw [hfactor] at hgF
  obtain ⟨x, hx, k, hk, rfl⟩ := hgF
  have hka : k • a=a := by simpa only [getVert_zero] using hK hk 0 (by omega)
  have he : (x*k) • a=x • a := by rw [mul_smul, hka]
  have hxne : x≠1 := by intro hh; rw [he, hh, one_smul] at hmove; exact hmove rfl
  obtain ⟨y, hy, u, hxx, hyy, hc, hu, hQu⟩ := hpairs x hx hxne
  obtain ⟨k, _, ht, hQt⟩ :=
    correct_path_reflection p n hlen K Q hK hQnorm (x*y*x) u hu hQu
  let t := k*u
  have hxn : x∈Subgroup.normalizer (Q : Set X) := by
    apply hQnorm
    change x • p.getVert n=p.getVert n
    have hh := (Subgroup.pCoreIn_le 2 _ hx) 0 (Nat.zero_le _)
    simpa only [getVert_zero] using hh
  have hyn : y∈Subgroup.normalizer (Q : Set X) :=
    hQnorm (pathRoot_fixes (p.take n) hy).1
  have hRQ := reflected_root_disjoint p n hlen Q hSQ hQnorm t ht
  rcases path_braid_exchange_or_centralizer p n hlen Q hRQ hSQ hx hy hxn hyn
      hxx hyy (by rw [← hc]; exact pow_orderOf_eq_one _) ht hQt with hh | hh
  · left
    simpa only [he] using hh
  · exact Or.inr ⟨x, hx, y, hy, hxx, hyy, hc, hh⟩

/-- The centralizer-free branch of the cubic local calculation gives the full chosen-apartment exchange condition. -/
theorem chosenApartmentExchange_of_cubic_pairs {Γ : SimpleGraph V} (T : Set V)
    (n : ℕ) (K : Subgroup X)
    (hK : ∀ k∈K, ∀ z∈T, k • z=z)
    (hlocal : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) →
      (pathFixer (X := X) (p.drop n) : Set X) =
        (pathRoot (X := X) (p.drop n) : Set X) * (K : Set X))
    (hn : 0<n)
    (hodd : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=n+1 →
      Odd (Nat.card (pathFixer (X := X) p)))
    (hQfix : ∀ a b, Γ.Adj a b →
      (MulAction.stabilizer X a).pCoreIn 2 ≤ MulAction.stabilizer X b)
    (hpairs : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) → ∀ x∈pathRoot (X := X) (p.drop n), x≠1 →
      ∃ y∈pathRoot (X := X) (p.take n), ∃ t : X,
        x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
        (∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) ∧
        (x*y*x)*t⁻¹∈(MulAction.stabilizer X (p.getVert n)).pCoreIn 2 ⊔ K)
    (hcentral : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) → ∀ x∈pathRoot (X := X) (p.drop n),
      ∀ y∈pathRoot (X := X) (p.take n), x*x=1 → y*y=1 → orderOf (x*y)=3 →
      ∀ h∈(MulAction.stabilizer X (p.getVert n)).pCoreIn 2,
        Commute x h → Commute y h → h=1) :
    ChosenApartmentExchange (X := X) Γ T n := by
  intro a b p hp hl hT g hg hmove
  have hfix : K ≤ pathFixer (X := X) p := by
    intro k hk j _
    exact hK k hk _ (hT _ (p.getVert_mem_support j))
  have hS := pathRoot_take_inf_vertexCore p hp n (by omega) hodd
    (hQfix _ _ (p.adj_getVert_succ (by omega)))
  rcases halfFixer_exchange_or_centralizer p n hl K
      ((MulAction.stabilizer X (p.getVert n)).pCoreIn 2) hfix
      (hlocal p hp hl hT) hS (vertexCore_normalized _)
      (hpairs p hp hl hT) g hg hmove with he | ⟨x,hx,y,hy,hxx,hyy,hc,z,hz,hzne,hxz,hyz⟩
  · exact he
  · exact (hzne (hcentral p hp hl hT x hx y hy hxx hyy hc z hz hxz hyz)).elim

end Theory.GroupTheory.WeakBNPair.RegularTree
