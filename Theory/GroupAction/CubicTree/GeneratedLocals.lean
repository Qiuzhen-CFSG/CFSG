module
public import Theory.GroupAction.RankTwoCosetGeometry
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Theory.Combinatorics.SimpleGraph.LocallyInjectiveTree

/-!
# Local subgroups generate exactly their endpoint stabilizers

Let P and Q fix adjacent vertices of a tree. Suppose that an element of
P fixes the other vertex precisely when it belongs to Q, and conversely.
Then P and Q are exactly the two endpoint stabilizers inside their join.

The rank-two coset graph of their join maps equivariantly into the tree.
The two intersection identities make this map injective on every neighbor
set. Connectedness and acyclicity then make it globally injective, so the
original point stabilizers are recovered from the coset stabilizers.
No finiteness or faithfulness of the acting group is needed.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.6),
printed pp.380--381; used in the terminal constructions of Sections 6.9
and 6.12.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry
namespace Theory.GroupAction.CubicTree
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

private def cosetVertexMap (F : Bool → Subgroup G) (v : Bool → V)
    (hv : ∀ i, F i ≤ MulAction.stabilizer G (v i)) (x : RankTwo.Vertex F) : V :=
  Quotient.lift (fun g : G => g • v x.type) (by
    intro a b hab
    have hf : (a⁻¹ * b) • v x.type = v x.type :=
      hv x.type (QuotientGroup.leftRel_apply.mp hab)
    apply (MulAction.injective a⁻¹)
    simpa only [mul_smul, inv_smul_smul] using hf.symm) x.coset

private theorem cosetVertexMap_base (F : Bool → Subgroup G) (v : Bool → V)
    (hv : ∀ i, F i ≤ MulAction.stabilizer G (v i)) (i : Bool) :
    cosetVertexMap F v hv (RankTwo.base F i) = v i := one_smul G _

private theorem cosetVertexMap_smul (F : Bool → Subgroup G) (v : Bool → V)
    (hv : ∀ i, F i ≤ MulAction.stabilizer G (v i))
    (g : G) (x : RankTwo.Vertex F) :
    cosetVertexMap F v hv (g • x) = g • cosetVertexMap F v hv x := by
  rcases x with ⟨i, q⟩
  induction q using Quotient.inductionOn with | h k => exact mul_smul g k (v i)

private def cosetGraphHom (hact : GraphAction Γ G)
    (F : Bool → Subgroup G) (v : Bool → V)
    (hv : ∀ i, F i ≤ MulAction.stabilizer G (v i))
    (hadj : Γ.Adj (v false) (v true)) : RankTwo.graph F →g Γ where
  toFun := cosetVertexMap F v hv
  map_rel' := by
    intro x y hxy
    obtain ⟨g, hgx, hgy⟩ := RankTwo.incident_common_translate F hxy.2
    rw [← hgx, ← hgy, cosetVertexMap_smul, cosetVertexMap_smul,
      cosetVertexMap_base, cosetVertexMap_base]
    apply hact.map_adj
    have hn := hxy.1
    cases hx : x.type <;> cases hy : y.type
    · exact (hn (hx.trans hy.symm)).elim
    · exact hadj
    · exact hadj.symm
    · exact (hn (hx.trans hy.symm)).elim

private theorem cosetGraphHom_locally_injective (hact : GraphAction Γ G)
    (F : Bool → Subgroup G) (v : Bool → V)
    (hv : ∀ i, F i ≤ MulAction.stabilizer G (v i))
    (hadj : Γ.Adj (v false) (v true))
    (hcross : ∀ i, F i ⊓ MulAction.stabilizer G (v (!i)) = F i ⊓ F (!i))
    (x : RankTwo.Vertex F) :
    Function.Injective ((cosetGraphHom hact F v hv hadj).mapNeighborSet x) := by
  rintro ⟨y, hy⟩ ⟨z, hz⟩ he
  apply Subtype.ext
  change y = z
  have hye : y.type = !x.type := by
    have hn := hy.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hze : z.type = !x.type := by
    have hn := hz.1
    cases hx : x.type <;> cases hz : z.type <;> simp_all
  obtain ⟨g, hgx, hgy⟩ := RankTwo.incident_common_translate F hy.2
  obtain ⟨k, hkx, hkz⟩ := RankTwo.incident_common_translate F hz.2
  let t := g⁻¹ * k
  have htfix : t • RankTwo.base F x.type = RankTwo.base F x.type := by
    calc
      t • RankTwo.base F x.type = g⁻¹ • (k • RankTwo.base F x.type) := mul_smul _ _ _
      _ = g⁻¹ • x := congrArg (g⁻¹ • ·) hkx
      _ = g⁻¹ • (g • RankTwo.base F x.type) := congrArg (g⁻¹ • ·) hgx.symm
      _ = RankTwo.base F x.type := inv_smul_smul _ _
  have htF : t ∈ F x.type := by
    exact stabilizer_base F x.type ▸
      (show t ∈ MulAction.stabilizer G (RankTwo.base F x.type) from htfix)
  have he' : g • v (!x.type) = k • v (!x.type) := by
    have hh := congrArg Subtype.val he
    change cosetVertexMap F v hv y = cosetVertexMap F v hv z at hh
    rw [← hgy, ← hkz, cosetVertexMap_smul, cosetVertexMap_smul,
      cosetVertexMap_base, cosetVertexMap_base, hye, hze] at hh
    exact hh
  have htv : t • v (!x.type) = v (!x.type) := by
    change (g⁻¹ * k) • v (!x.type) = _
    rw [mul_smul, ← he', inv_smul_smul]
  have htJ : t ∈ F (!x.type) :=
    (show t ∈ F x.type ⊓ F (!x.type) from hcross x.type ▸ ⟨htF, htv⟩).2
  have htbase : t • RankTwo.base F (!x.type) = RankTwo.base F (!x.type) := by
    change t ∈ MulAction.stabilizer G (RankTwo.base F (!x.type))
    exact (stabilizer_base F (!x.type)).symm ▸ htJ
  rw [hye] at hgy
  rw [hze] at hkz
  rw [← hgy, ← hkz]
  apply (MulAction.injective g⁻¹)
  calc
    g⁻¹ • (g • RankTwo.base F (!x.type)) = RankTwo.base F (!x.type) := inv_smul_smul _ _
    _ = t • RankTwo.base F (!x.type) := htbase.symm
    _ = g⁻¹ • (k • RankTwo.base F (!x.type)) := mul_smul _ _ _

private theorem stabilizer_eq_of_generated_locals
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (F : Bool → Subgroup G) (v : Bool → V)
    (hv : ∀ i, F i ≤ MulAction.stabilizer G (v i))
    (hadj : Γ.Adj (v false) (v true))
    (hcross : ∀ i, F i ⊓ MulAction.stabilizer G (v (!i)) = F i ⊓ F (!i))
    (hgen : F false ⊔ F true = ⊤) (i : Bool) :
    MulAction.stabilizer G (v i) = F i := by
  let f := cosetGraphHom hact F v hv hadj
  have hi : Function.Injective f :=
    f.injective_of_locally_injective_of_acyclic (RankTwo.connected F hgen) hΓ
      (cosetGraphHom_locally_injective hact F v hv hadj hcross)
  apply le_antisymm ?_ (hv i)
  intro g hg
  have hfix : g • RankTwo.base F i = RankTwo.base F i := by
    apply hi
    change cosetVertexMap F v hv (g • RankTwo.base F i) =
      cosetVertexMap F v hv (RankTwo.base F i)
    rw [cosetVertexMap_smul, cosetVertexMap_base]
    exact hg
  exact stabilizer_base F i ▸
    (show g ∈ MulAction.stabilizer G (RankTwo.base F i) from hfix)

/-- Local subgroups satisfying the two exact overlap conditions are the
endpoint stabilizers inside their generated subgroup. -/
theorem sup_inf_stabilizers_eq (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {a b : V} (hab : Γ.Adj a b) (P Q : Subgroup G)
    (hP : P ≤ MulAction.stabilizer G a) (hQ : Q ≤ MulAction.stabilizer G b)
    (hPQ : P ⊓ MulAction.stabilizer G b = P ⊓ Q)
    (hQP : Q ⊓ MulAction.stabilizer G a = P ⊓ Q) :
    (P ⊔ Q) ⊓ MulAction.stabilizer G a = P ∧
      (P ⊔ Q) ⊓ MulAction.stabilizer G b = Q := by
  let H := P ⊔ Q
  let F : Bool → Subgroup H := fun i => if i then Q.subgroupOf H else P.subgroupOf H
  let v : Bool → V := fun i => if i then b else a
  have ha : GraphAction Γ H := ⟨fun g _ _ h => hact.map_adj (g : G) h⟩
  have hv : ∀ i, F i ≤ MulAction.stabilizer H (v i) := by
    intro i
    cases i
    · exact fun g hg => hP hg
    · exact fun g hg => hQ hg
  have hcross : ∀ i, F i ⊓ MulAction.stabilizer H (v (!i)) = F i ⊓ F (!i) := by
    intro i
    cases i
    · ext g
      exact SetLike.ext_iff.mp hPQ (g : G)
    · ext g
      exact SetLike.ext_iff.mp (hQP.trans (inf_comm P Q)) (g : G)
  have hgen : F false ⊔ F true = ⊤ := by
    change P.subgroupOf H ⊔ Q.subgroupOf H = ⊤
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show P ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show Q ≤ H from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hs := stabilizer_eq_of_generated_locals hΓ ha F v hv hab hcross hgen
  constructor
  · apply le_antisymm ?_ (le_inf le_sup_left hP)
    intro g hg
    have hm : (⟨g, hg.1⟩ : H) ∈ MulAction.stabilizer H a := hg.2
    have he := hs false
    change MulAction.stabilizer H a = P.subgroupOf H at he
    exact (show (⟨g, hg.1⟩ : H) ∈ P.subgroupOf H from he ▸ hm)
  · apply le_antisymm ?_ (le_inf le_sup_right hQ)
    intro g hg
    have hm : (⟨g, hg.1⟩ : H) ∈ MulAction.stabilizer H b := hg.2
    have he := hs true
    change MulAction.stabilizer H b = Q.subgroupOf H at he
    exact (show (⟨g, hg.1⟩ : H) ∈ Q.subgroupOf H from he ▸ hm)

end Theory.GroupAction.CubicTree
