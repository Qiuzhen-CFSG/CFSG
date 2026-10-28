module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalPathExchange
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalActor

/-!
# Transporting natural coordinates to apartment midpoints

On a nonbranching apartment, an actor mapping the first edge maps a whole
simple path. An involution fixing the midpoint and moving one neighbor
therefore reverses an even path. Conjugation transports the actual local
actor, its quotient and entire vertex two-core, both half-path radicals,
and the same Cartan marking into `NaturalPathCoordinates`.

The source application constructs the transporter from the marked apartment
edge and applies this to DGS (14.13). No naturality of a quotient by a central
subgroup is substituted for naturality of the full kernel.
Source: DGS, *Groups and Graphs* (1985), (14.12)--(14.13), pp.217--218.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk Subgroup
open scoped MatrixGroups
open NaturalCubic
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {T : Set V}

/-- In a nonbranching apartment, a prescribed actor mapping the initial edge
maps every vertex of two equally long simple paths. -/
theorem maps_path_of_first_edge
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T)
    {a b c e : V} (p : Γ.Walk a b) (q : Γ.Walk c e)
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length=q.length)
    (hpT : ∀ z∈p.support, z∈T) (hqT : ∀ z∈q.support, z∈T)
    (g : X) (hpres : ∀ z∈T, g • z∈T)
    (hzero : g • a=c) (hone : g • p.getVert 1=q.getVert 1) :
    ∀ k≤p.length, g • p.getVert k=q.getVert k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _; simpa only [getVert_zero] using hzero
  | one => intro _; exact hone
  | more k ih₀ ih₁ =>
    intro hk
    have he₀ := ih₀ (by omega : k≤p.length)
    have he₁ := ih₁ (by omega : k+1≤p.length)
    have hback : Γ.Adj (q.getVert (k+1)) (g • p.getVert k) := by
      rw [←he₁]
      exact hact _ (p.adj_getVert_succ (by omega)).symm
    have hnext : Γ.Adj (q.getVert (k+1)) (g • p.getVert (k+2)) := by
      rw [←he₁]
      exact hact _ (p.adj_getVert_succ (by omega))
    have hne : g • p.getVert k≠g • p.getVert (k+2) := by
      intro he
      have := hp.getVert_injOn (by omega : k≤p.length) hk ((MulAction.toPerm g).injective he)
      omega
    rcases hline _ (hqT _ (q.getVert_mem_support _))
      _ (hpres _ (hpT _ (p.getVert_mem_support _)))
      _ (hpres _ (hpT _ (p.getVert_mem_support _)))
      _ (hqT _ (q.getVert_mem_support _)) hback hnext
      (q.adj_getVert_succ (by omega)) hne with he | he
    · rw [he₀] at he
      have := hq.getVert_injOn (by omega : k+2≤q.length) (by omega : k≤q.length) he
      omega
    · exact he.symm

/-- An involution preserving a line, fixing the midpoint, and moving one
neighbor reverses the entire even path through that midpoint. -/
theorem reverses_path_of_moves_midpoint_neighbor
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) {a b : V}
    (p : Γ.Walk a b) (hp : p.IsPath) (n : ℕ) (hn : 0<n) (hlen : p.length=2*n)
    (hpT : ∀ z∈p.support, z∈T) (t : X) (htt : t*t=1)
    (hpres : ∀ z∈T, t • z∈T) (hfix : t • p.getVert n=p.getVert n)
    (hmove : t • p.getVert (n+1)≠p.getVert (n+1)) :
    ∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k) := by
  have hprev : Γ.Adj (p.getVert n) (p.getVert (n-1)) := by
    simpa only [Nat.sub_add_cancel hn] using (p.adj_getVert_succ (by omega : n-1<p.length)).symm
  have hnext := p.adj_getVert_succ (by omega : n<p.length)
  have hne : p.getVert (n-1)≠p.getVert (n+1) := by
    intro he
    have := hp.getVert_injOn (by omega : n-1≤p.length) (by omega : n+1≤p.length) he
    omega
  have hsend : t • p.getVert (n+1)=p.getVert (n-1) := by
    rcases hline _ (hpT _ (p.getVert_mem_support _)) _ (hpT _ (p.getVert_mem_support _))
      _ (hpT _ (p.getVert_mem_support _)) _ (hpres _ (hpT _ (p.getVert_mem_support _)))
      hprev hnext (by simpa only [hfix] using hact t hnext) hne with he | he
    · exact he
    · exact (hmove he).elim
  have hhalf : ∀ k≤n, t • p.getVert (n+k)=p.getVert (n-k) := by
    have hpD : ∀ z∈(p.drop n).support, z∈T := by
      intro z hz
      rw [drop_support_eq_support_drop_min] at hz
      exact hpT z (List.mem_of_mem_drop hz)
    have hpR : ∀ z∈(p.take n).reverse.support, z∈T := by
      intro z hz
      simp only [support_reverse,List.mem_reverse] at hz
      rw [support_take] at hz
      exact hpT z (List.mem_of_mem_take hz)
    have he := maps_path_of_first_edge hact hline (p.drop n) (p.take n).reverse
      (hp.drop n) (hp.take n).reverse (by simp only [drop_length,length_reverse,take_length,hlen]; omega)
      hpD hpR t hpres hfix (by
        simp only [drop_getVert,getVert_reverse,take_length,hlen,take_getVert]
        simpa only [show min n (2*n)=n by omega, show min n (n-1)=n-1 by omega] using hsend)
    intro k hk
    have hh := he k (by rw [drop_length,hlen]; omega)
    simpa only [drop_getVert,getVert_reverse,take_length,hlen,take_getVert,
      show min n (2*n)=n by omega,show min n (n-k)=n-k by omega] using hh
  intro k hk
  by_cases hnk : n≤k
  · have he := hhalf (k-n) (by omega)
    simpa only [show n+(k-n)=k by omega, show n-(k-n)=2*n-k by omega] using he
  · have he := congrArg (t • ·) (hhalf (n-k) (by omega))
    rw [←mul_smul,htt,one_smul] at he
    have he' : p.getVert (2*n-k)=t • p.getVert k := by
      simpa only [show n+(n-k)=2*n-k by omega, show n-(n-k)=k by omega] using he
    exact he'.symm


/-- Transport a marked local actor to the actual midpoint. All roots, the
whole vertex two-core and the Cartan use the same conjugating element. -/
def naturalPathCoordinates_of_conjugate
    {F : Type*} [Field F] [CharP F 2] {a b v : V}
    (p : Γ.Walk a b) (n : ℕ) (K H R S : Subgroup X)
    (hH : H≤MulAction.stabilizer X v)
    (hQ : (MulAction.stabilizer X v).pCoreIn 2≤H)
    (hR : R≤H) (hS : S≤H)
    (π : H →* SL(2,F))
    (hker : π.ker=((MulAction.stabilizer X v).pCoreIn 2).subgroupOf H)
    (nat : NaturalKernel π)
    (hupper : ∀ x : H, (x:X)∈R → ∃ a : F, π x=upper a)
    (hlower : ∀ y : H, (y:X)∈S → ∃ a : F, π y=lower a)
    (honto : ∀ a : F, ∃ y : H, (y:X)∈S ∧ π y=lower a)
    (hdiag : ∀ a : F, ∀ ha : a≠0,
      Matrix.SpecialLinearGroup.diag2 a ha∈(K.subgroupOf H).map π)
    (t : H) (g : X) (hg : g∈normalizer (K : Set X))
    (hv : g • v=p.getVert n)
    (hr : R.map (MulAut.conj g).toMonoidHom=pathRoot (X := X) (p.drop n))
    (hs : S.map (MulAut.conj g).toMonoidHom=pathRoot (X := X) (p.take n))
    (ht : ∀ k≤2*n, (g*(t:X)*g⁻¹) • p.getVert k=p.getVert (2*n-k)) :
    NaturalPathCoordinates p n K := by
  let φ := (MulAut.conj g).toMonoidHom
  let H' := H.map φ
  let e : H ≃* H' := H.equivMapOfInjective φ (MulAut.conj g).injective
  have he (x : H) : (e x:X)=φ x := rfl
  have hcore : ((MulAction.stabilizer X v).pCoreIn 2).map φ=
      (MulAction.stabilizer X (p.getVert n)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      ←MulAction.stabilizer_smul_eq_stabilizer_map_conj,hv]
  have hH' : H'≤MulAction.stabilizer X (p.getVert n) := by
    rw [←hv,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact map_mono hH
  have hQ' : (MulAction.stabilizer X (p.getVert n)).pCoreIn 2≤H' := by
    rw [←hcore]
    exact map_mono hQ
  have hπker : (π.comp e.symm.toMonoidHom).ker=
      ((MulAction.stabilizer X (p.getVert n)).pCoreIn 2).subgroupOf H' := by
    ext x
    obtain ⟨y,rfl⟩ := e.surjective x
    change π (e.symm (e y))=1 ↔ (e y:X)∈(MulAction.stabilizer X (p.getVert n)).pCoreIn 2
    rw [e.symm_apply_apply,←hcore,he]
    change y∈π.ker ↔ φ y∈((MulAction.stabilizer X v).pCoreIn 2).map φ
    rw [hker]
    constructor
    · intro hy; exact mem_map_of_mem φ hy
    · rintro ⟨z,hz,hz'⟩
      have hz'' : z=(y:X) := (MulAut.conj g).injective hz'
      rwa [hz''] at hz
  refine {
    F := F
    localGroup := H'
    local_le := hH'
    core_le := hQ'
    upper_le := ?_
    lower_le := ?_
    quotient := π.comp e.symm.toMonoidHom
    kernel_eq := hπker
    natural := nat.ofEquiv e.symm
    upper_image := ?_
    lower_elements := ?_
    lower_image := ?_
    diagonal_image := ?_
    reflection := e t
    reverses := ht }
  · rw [←hr]; exact map_mono hR
  · rw [←hs]; exact map_mono hS
  · intro x hx
    obtain ⟨y,rfl⟩ := e.surjective x
    rw [←hr,he] at hx
    obtain ⟨z,hz,hz'⟩ := hx
    have hz'' : z=(y:X) := (MulAut.conj g).injective hz'
    rw [hz''] at hz
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hupper y hz
  · intro x hx
    obtain ⟨y,rfl⟩ := e.surjective x
    rw [←hs,he] at hx
    obtain ⟨z,hz,hz'⟩ := hx
    have hz'' : z=(y:X) := (MulAut.conj g).injective hz'
    rw [hz''] at hz
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hlower y hz
  · intro a
    obtain ⟨y,hy,hπy⟩ := honto a
    refine ⟨e y,?_,?_⟩
    · rw [←hs,he]; exact mem_map_of_mem φ hy
    · simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hπy
  · intro a ha
    obtain ⟨k,hk,hπk⟩ := hdiag a ha
    refine ⟨e k,?_,?_⟩
    · exact (mem_normalizer_iff.mp hg k).mp hk
    · simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hπk

end Theory.GroupTheory.WeakBNPair.RegularTree
