module
public import Theory.GroupAction.RankTwoCosetGeometry.CommutingSeeds
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Reciprocal seeds from a coset graph

Minimize a noncommuting pair over both types of vertices. Along a shorter
walk the two seeds commute, so each endpoint seed fixes the opposite vertex
and lies in the two-core of an edge at that vertex. Translating both edges
to the standard edge produces one conjugator with both reciprocal bounds.
Core freeness supplies a noncommuting pair: otherwise path propagation puts
every seed in the global action kernel.

Source: Aschbacher–Smith 13.4.17, printed p.914, using F.7.3 and F.7.9.
The argument works for arbitrary groups and normal abelian seeds; no
classification or finite-group hypotheses enter this geometric step.
-/

public section
open Subgroup
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private def vertexSeed (F N : Bool → Subgroup G) (v : Vertex F) : Subgroup G :=
  ⨆ g : G, ⨆ (_ : g • base F v.type = v), (N v.type).conjBy g

private theorem vertexSeed_translate (F N : Bool → Subgroup G)
    (hn : ∀ i, F i ≤ normalizer (N i : Set G)) (i : Bool) (g : G) :
    vertexSeed F N (g • base F i) = (N i).conjBy g := by
  apply le_antisymm
  · refine iSup_le fun k => iSup_le fun hk => ?_
    change k • base F i = g • base F i at hk
    have hm : g⁻¹*k ∈ F i := by
      rw [← CosetGeometry.stabilizer_base F i]
      change (g⁻¹*k) • base F i = base F i
      rw [mul_smul,hk,inv_smul_smul]
    have he := mem_normalizer_iff_map_conj_eq.mp (hn i hm)
    change (N i).conjBy (g⁻¹*k) = N i at he
    have hh := congrArg (fun S : Subgroup G => S.conjBy g) he
    rw [←conjBy_mul] at hh
    change (N i).conjBy k ≤ (N i).conjBy g
    simpa only [mul_inv_cancel_left] using hh.le
  · exact le_iSup_of_le g (le_iSup_of_le rfl le_rfl)

private theorem short_walk_fixes {Ω : Type*} (Γ : SimpleGraph Ω)
    (A N : Ω → Subgroup G) (hNA : ∀ v, N v ≤ A v)
    (hedge : ∀ v w, Γ.Adj v w → A v ⊓ centralizer (N v : Set G) ≤ A w)
    (n : ℕ)
    (hshort : ∀ v w, ∀ p : Γ.Walk v w, p.length < n → ⁅N v,N w⁆ = ⊥)
    {v w : Ω} (p : Γ.Walk v w) (hp : p.length ≤ n) : N w ≤ A v := by
  induction p with
  | nil => exact hNA _
  | @cons v t w hvt tail ih =>
    have ht : tail.length < n := by simp only [SimpleGraph.Walk.length_cons] at hp; omega
    have hc := commutator_eq_bot_iff_le_centralizer.mp (hshort t w tail ht)
    exact (le_inf (ih (by omega)) (le_centralizer_iff.mp hc)).trans (hedge t v hvt.symm)

/-- A shortest noncommuting pair, with minimization over all vertices,
places each seed in the two-core of an edge at the opposite endpoint. -/
theorem minimal_noncommuting_seed_edges {Ω : Type*} (Γ : SimpleGraph Ω)
    (A N : Ω → Subgroup G) (hNA : ∀ v, N v ≤ A v)
    (habel : ∀ v, ⁅N v,N v⁆ = ⊥)
    (hedge : ∀ v w, Γ.Adj v w →
      A v ⊓ centralizer (N v : Set G) ≤ (A v ⊓ A w).pCoreIn 2)
    (hex : ∃ v w, ∃ _p : Γ.Walk v w, ⁅N v,N w⁆ ≠ ⊥) :
    ∃ v v' w w', Γ.Adj v v' ∧ Γ.Adj w w' ∧
      N w ≤ (A v ⊓ A v').pCoreIn 2 ∧
      N v ≤ (A w ⊓ A w').pCoreIn 2 ∧ ⁅N v,N w⁆ ≠ ⊥ := by
  classical
  have he : ∃ n : ℕ, ∃ v w, ∃ p : Γ.Walk v w, p.length = n ∧ ⁅N v,N w⁆ ≠ ⊥ := by
    obtain ⟨v,w,p,hp⟩ := hex
    exact ⟨p.length,v,w,p,rfl,hp⟩
  obtain ⟨v,w,p,hplen,hmove⟩ := Nat.find_spec he
  have hshort : ∀ a b, ∀ q : Γ.Walk a b, q.length < Nat.find he → ⁅N a,N b⁆ = ⊥ := by
    intro a b q hq
    by_contra hc
    exact (Nat.find_min he hq) ⟨a,b,q,rfl,hc⟩
  have hfix {a b} (q : Γ.Walk a b) (hq : q.length ≤ Nat.find he) : N b ≤ A a :=
    short_walk_fixes Γ A N hNA
    (fun a b hab => (hedge a b hab).trans ((pCoreIn_le 2 _).trans inf_le_right))
    (Nat.find he) hshort q hq
  have first : ∀ a b, ∀ q : Γ.Walk a b, q.length = Nat.find he → ⁅N a,N b⁆ ≠ ⊥ →
      ∃ a', Γ.Adj a a' ∧ N b ≤ (A a ⊓ A a').pCoreIn 2 := by
    intro a b q hq hc
    cases q with
    | nil => exact (hc (habel a)).elim
    | @cons a t b hat tail =>
      have ht : tail.length < Nat.find he := by simp only [SimpleGraph.Walk.length_cons] at hq; omega
      have hf : N b ≤ A t := hfix tail (by omega)
      have hm := commutator_eq_bot_iff_le_centralizer.mp (hshort t b tail ht)
      refine ⟨t,hat,?_⟩
      simpa only [inf_comm (A t) (A a)] using
        (le_inf hf (le_centralizer_iff.mp hm)).trans (hedge t a hat.symm)
  obtain ⟨v',hv,hvcore⟩ := first v w p hplen hmove
  obtain ⟨w',hw,hwcore⟩ := first w v p.reverse (by simpa using hplen)
    (by rwa [commutator_comm])
  exact ⟨v,v',w,w',hv,hw,hvcore,hwcore,hmove⟩



/-- Both types participate in the minimum. The conjugator in the two
reciprocal containments is the same relative edge transporter. -/
theorem exists_reciprocal_noncommuting_seeds (F N : Bool → Subgroup G)
    (hgen : F false ⊔ F true = ⊤)
    (hcore : (F false ⊓ F true).normalCore = ⊥)
    (hle : ∀ i, N i ≤ F i)
    (hn : ∀ i, F i ≤ normalizer (N i : Set G))
    (habel : ∀ i, ⁅N i,N i⁆ = ⊥)
    (hne : N false ≠ ⊥)
    (hC : ∀ i, F i ⊓ centralizer (N i : Set G) ≤ (F false ⊓ F true).pCoreIn 2) :
    ∃ i j, ∃ g : G, (N j).conjBy g ≤ (F false ⊓ F true).pCoreIn 2 ∧
      N i ≤ ((F false ⊓ F true).pCoreIn 2).conjBy g ∧
      ⁅N i,(N j).conjBy g⁆ ≠ ⊥ := by
  classical
  let A := stabilizer F
  let S := vertexSeed F N
  have hSA (v : Vertex F) : S v ≤ A v := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    dsimp only [S,A]
    rw [←hg,vertexSeed_translate F N hn,stabilizer_translate]
    simpa only [stabilizer,CosetGeometry.stabilizer_base,conjBy] using map_mono (hle v.type)
  have hnorm (v : Vertex F) : A v ≤ normalizer (S v : Set G) := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    dsimp only [S,A]
    rw [←hg,vertexSeed_translate F N hn,stabilizer_translate]
    simp only [stabilizer,CosetGeometry.stabilizer_base]
    exact (map_mono (hn _)).trans (le_normalizer_map _)
  have hab (v : Vertex F) : ⁅S v,S v⁆ = ⊥ := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    dsimp only [S]
    rw [←hg,vertexSeed_translate F N hn]
    change ⁅(N _).map _,(N _).map _⁆ = _
    rw [←map_commutator,habel,map_bot]
  have hedge (v w : Vertex F) (hv : (graph F).Adj v w) :
      A v ⊓ centralizer (S v : Set G) ≤ (A v ⊓ A w).pCoreIn 2 := by
    obtain ⟨g,hg,hg'⟩ := incident_common_translate F hv.2
    change stabilizer F v ⊓ centralizer (vertexSeed F N v : Set G) ≤
      (stabilizer F v ⊓ stabilizer F w).pCoreIn 2
    rw [←hg,←hg',vertexSeed_translate F N hn,stabilizer_translate,stabilizer_translate]
    simp only [stabilizer,CosetGeometry.stabilizer_base]
    simp only [conjBy]
    rw [map_inf_centralizer_of_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      ←map_inf _ _ _ (MulAut.conj g).injective,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    apply map_mono
    have he : F v.type ⊓ F w.type = F false ⊓ F true := by
      have ht := hv.1
      cases hi : v.type <;> cases hj : w.type <;> simp_all only [inf_comm]
    rw [he]
    exact hC _
  have hex : ∃ v w, ∃ _p : (graph F).Walk v w, ⁅S v,S w⁆ ≠ ⊥ := by
    by_contra! hc
    have hcomm (v w : Vertex F) : ⁅S v,S w⁆ = ⊥ := by
      obtain ⟨p⟩ := (connected F hgen) v w
      exact hc v w p
    have hall (v w : Vertex F) : S v ≤ A w := by
      obtain ⟨p⟩ := (connected F hgen) v w
      exact (seeds_propagate (graph F) A S hSA hnorm
        (fun a b hab => (hedge a b hab).trans ((pCoreIn_le 2 _).trans inf_le_right))
        (fun a b _ => hcomm a b) p).1
    have hk : N false ≤ (MulAction.toPermHom G (Vertex F)).ker := by
      intro x hx
      apply Equiv.Perm.ext
      intro w
      have hxS : x ∈ S (base F false) := by
        have he := vertexSeed_translate F N hn false 1
        simp only [one_smul,conjBy_one] at he
        change x ∈ vertexSeed F N (base F false)
        rw [he]
        exact hx
      exact hall (base F false) w hxS
    rw [global_kernel,hcore] at hk
    exact hne (bot_unique hk)
  obtain ⟨v,v',w,w',hv,hw,hvw,hwv,hmove⟩ :=
    minimal_noncommuting_seed_edges (graph F) A S hSA hab hedge hex
  obtain ⟨a,ha,ha'⟩ := incident_common_translate F hv.2
  obtain ⟨b,hb,hb'⟩ := incident_common_translate F hw.2
  let R := (F false ⊓ F true).pCoreIn 2
  have edge (x y : Vertex F) (hxy : (graph F).Adj x y)
      (c : G) (hx : c • base F x.type = x) (hy : c • base F y.type = y) :
      (A x ⊓ A y).pCoreIn 2 = R.conjBy c := by
    change (stabilizer F x ⊓ stabilizer F y).pCoreIn 2 = _
    rw [←hx,←hy,stabilizer_translate,stabilizer_translate]
    simp only [stabilizer,CosetGeometry.stabilizer_base]
    rw [←map_inf _ _ _ (MulAut.conj c).injective,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj c).injective]
    have he : F x.type ⊓ F y.type = F false ⊓ F true := by
      have ht := hxy.1
      cases hi : x.type <;> cases hj : y.type <;> simp_all only [inf_comm]
    rw [he]
    rfl
  rw [edge v v' hv a ha ha'] at hvw
  rw [edge w w' hw b hb hb'] at hwv
  have sv : S v = (N v.type).conjBy a := by
    change vertexSeed F N v = _
    rw [←ha,vertexSeed_translate F N hn]
    rfl
  have sw : S w = (N w.type).conjBy b := by
    change vertexSeed F N w = _
    rw [←hb,vertexSeed_translate F N hn]
    rfl
  rw [sw] at hvw
  rw [sv] at hwv
  refine ⟨v.type,w.type,a⁻¹*b,?_,?_,?_⟩
  · have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hvw
    change ((N w.type).conjBy b).conjBy a⁻¹ ≤ (R.conjBy a).conjBy a⁻¹ at hh
    simpa only [←conjBy_mul,inv_mul_cancel,conjBy_one] using hh
  · have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hwv
    change ((N v.type).conjBy a).conjBy a⁻¹ ≤ (R.conjBy b).conjBy a⁻¹ at hh
    simpa only [←conjBy_mul,inv_mul_cancel,conjBy_one] using hh
  · intro he
    apply hmove
    rw [sv,sw]
    have hh := congrArg (map (MulAut.conj a).toMonoidHom) he
    rw [map_commutator,map_bot] at hh
    change ⁅(N v.type).conjBy a,((N w.type).conjBy (a⁻¹*b)).conjBy a⁆ = ⊥ at hh
    simpa only [←conjBy_mul,mul_inv_cancel_left] using hh

/-- Construct the actual coset graph inside the join, preserving the ambient
edge core and both ambient seed subgroups. -/
theorem exists_reciprocal_noncommuting_seeds_in_join (F N : Bool → Subgroup G)
    (hle : ∀ i, N i ≤ F i)
    (hn : ∀ i, F i ≤ normalizer (N i : Set G))
    (habel : ∀ i, ⁅N i,N i⁆ = ⊥)
    (hne : N false ≠ ⊥)
    (hC : ∀ i, F i ⊓ centralizer (N i : Set G) ≤ (F false ⊓ F true).pCoreIn 2)
    (hcommon : ∀ A : Subgroup G, A ≤ F false →
      F false ⊔ F true ≤ normalizer (A : Set G) → A = ⊥) :
    ∃ i j, ∃ g ∈ F false ⊔ F true,
      (N j).conjBy g ≤ (F false ⊓ F true).pCoreIn 2 ∧
      N i ≤ ((F false ⊓ F true).pCoreIn 2).conjBy g ∧
      ⁅N i,(N j).conjBy g⁆ ≠ ⊥ := by
  let J := F false ⊔ F true
  let A : Bool → Subgroup J := fun i => (F i).subgroupOf J
  let S : Bool → Subgroup J := fun i => (N i).subgroupOf J
  have hF (i) : F i ≤ J := by cases i; exact le_sup_left; exact le_sup_right
  have hN (i) : N i ≤ J := (hle i).trans (hF i)
  have hgen : A false ⊔ A true = ⊤ := by
    rw [←subgroupOf_sup (hF false) (hF true),subgroupOf_self]
  have hcore : (A false ⊓ A true).normalCore = ⊥ := by
    let C := (A false ⊓ A true).normalCore
    have hCM : C.map J.subtype ≤ F false := by
      rintro x ⟨x,hx,rfl⟩
      exact ((A false ⊓ A true).normalCore_le hx).1
    have hnorm : J ≤ normalizer (C.map J.subtype : Set G) := by
      have hh := C.le_normalizer_map J.subtype
      rw [C.normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    have he := hcommon (C.map J.subtype) hCM hnorm
    apply map_injective J.subtype_injective
    simpa only [map_bot] using he
  have hSN (i) : A i ≤ normalizer (S i : Set J) := by
    rw [←subgroupOf_normalizer_eq (hN i)]
    exact fun x hx => hn i hx
  have hSC (i) : A i ⊓ centralizer (S i : Set J) ≤ (A false ⊓ A true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [←map_inf_centralizer_of_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (hF i),map_subgroupOf_eq_of_le (hN i),
      map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (hF false),map_subgroupOf_eq_of_le (hF true)]
    exact hC i
  have hSabel (i) : ⁅S i,S i⁆ = ⊥ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le (hN i),habel,map_bot]
  have hSne : S false ≠ ⊥ := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le (hN false),map_bot] at hh
    exact hne hh
  obtain ⟨i,j,g,hg,hg',hc⟩ := exists_reciprocal_noncommuting_seeds A S hgen hcore
    (fun i x hx => hle i hx) hSN hSabel hSne hSC
  have cmap (Y : Subgroup J) : (Y.conjBy g).map J.subtype = (Y.map J.subtype).conjBy g.val := by
    simp only [conjBy,map_map]
    rfl
  have coremap : ((A false ⊓ A true).pCoreIn 2).map J.subtype =
      (F false ⊓ F true).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (hF false),map_subgroupOf_eq_of_le (hF true)]
  refine ⟨i,j,g.val,g.property,?_,?_,?_⟩
  · have hh := map_mono (f := J.subtype) hg
    rwa [cmap,map_subgroupOf_eq_of_le (hN j),coremap] at hh
  · have hh := map_mono (f := J.subtype) hg'
    rwa [map_subgroupOf_eq_of_le (hN i),cmap,coremap] at hh
  · intro he
    apply hc
    apply map_injective J.subtype_injective
    rwa [map_commutator,cmap,map_subgroupOf_eq_of_le (hN i),
      map_subgroupOf_eq_of_le (hN j),map_bot]

/-- Eliminating both second-type and mixed endpoints leaves a noncommuting
pair of first-type seeds with both original reciprocal edge containments. -/
theorem exists_first_reciprocal_noncommuting_seeds (M X V U : Subgroup G)
    (hV : V ≤ M) (hU : U ≤ X)
    (hnV : M ≤ normalizer (V : Set G)) (hnU : X ≤ normalizer (U : Set G))
    (habV : ⁅V,V⁆ = ⊥) (habU : ⁅U,U⁆ = ⊥) (hne : V ≠ ⊥)
    (hCV : M ⊓ centralizer (V : Set G) ≤ (M ⊓ X).pCoreIn 2)
    (hCU : X ⊓ centralizer (U : Set G) ≤ (M ⊓ X).pCoreIn 2)
    (hcommon : ∀ A : Subgroup G, A ≤ M → M ⊔ X ≤ normalizer (A : Set G) → A = ⊥)
    (hmixed : ∀ g : G, U.conjBy g ≤ (M ⊓ X).pCoreIn 2 →
      V ≤ ((M ⊓ X).pCoreIn 2).conjBy g → ⁅V,U.conjBy g⁆ = ⊥)
    (hsecond : ∀ g : G, U.conjBy g ≤ (M ⊓ X).pCoreIn 2 →
      U ≤ ((M ⊓ X).pCoreIn 2).conjBy g → ⁅U,U.conjBy g⁆ = ⊥) :
    ∃ g ∈ M ⊔ X, V.conjBy g ≤ (M ⊓ X).pCoreIn 2 ∧
      V ≤ ((M ⊓ X).pCoreIn 2).conjBy g ∧ ⁅V,V.conjBy g⁆ ≠ ⊥ := by
  let F : Bool → Subgroup G := fun i => if i then X else M
  let N : Bool → Subgroup G := fun i => if i then U else V
  obtain ⟨i,j,g,hg,h₁,h₂,hc⟩ := exists_reciprocal_noncommuting_seeds_in_join F N
    (by intro i; cases i; exact hV; exact hU)
    (by intro i; cases i; exact hnV; exact hnU)
    (by intro i; cases i; exact habV; exact habU) hne
    (by intro i; cases i; exact hCV; exact hCU) hcommon
  cases i <;> cases j
  · exact ⟨g,hg,h₁,h₂,hc⟩
  · exact (hc (hmixed g h₁ h₂)).elim
  · have h₁' : U.conjBy g⁻¹ ≤ (M ⊓ X).pCoreIn 2 := by
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₂
      change U.conjBy g⁻¹ ≤ (((M ⊓ X).pCoreIn 2).conjBy g).conjBy g⁻¹ at hh
      simpa only [←conjBy_mul,inv_mul_cancel,conjBy_one] using hh
    have h₂' : V ≤ ((M ⊓ X).pCoreIn 2).conjBy g⁻¹ := by
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₁
      change (V.conjBy g).conjBy g⁻¹ ≤ ((M ⊓ X).pCoreIn 2).conjBy g⁻¹ at hh
      simpa only [←conjBy_mul,inv_mul_cancel,conjBy_one] using hh
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) (hmixed g⁻¹ h₁' h₂')
    rw [map_commutator,map_bot] at hh
    change ⁅V.conjBy g,(U.conjBy g⁻¹).conjBy g⁆ = ⊥ at hh
    rw [←conjBy_mul,mul_inv_cancel,conjBy_one,commutator_comm] at hh
    exact (hc hh).elim
  · exact (hc (hsecond g h₁ h₂)).elim
end Subgroup.CosetGeometry.RankTwo
