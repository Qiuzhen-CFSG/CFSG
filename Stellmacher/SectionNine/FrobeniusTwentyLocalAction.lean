module
public import Stellmacher.SectionNine.CubicLocalAction
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup
public import Theory.GroupAction.FivePointOrderFour

/-!
# Edge transitivity in the native degree-five local action

If a vertex stabilizer of the genuine Section Seven coset graph has the
faithful C5 semidirect C4 quotient by its two-core, each incident edge
stabilizer acts transitively on the other four neighbors. The conclusion
returns an element of the actual ambient edge stabilizer carrying the
supplied left neighbor to the supplied right neighbor.

The true Sylow-two edge containment, properness and quotient order twenty
force edge index five. Local transitivity gives exactly five neighbors.
Counting makes the edge a two-group, so the shared native neighbor-action
kernel theorem identifies its kernel with the vertex two-core. The literal
edge image in the supplied quotient has order four and cannot have exponent
two, by the elementary-subgroup bound for C5 semidirect C4. Thus an actual
edge lift induces an order-four permutation fixing the root. A kernel-checked
five-point permutation theorem supplies a power moving the other supplied
neighbors. Taking its inverse respects the graph's right-action convention.
No canonical permutation action is substituted for the native graph action.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.65, the
predecessor choice after (20) in the proof of (10.1), using the local graph
facts (7.1) and (7.3). This lemma has no critical-path or Section Ten input.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup
universe u v
variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}

private theorem edge_index_five
    (h7 : SectionSevenHypotheses G S P1 P2) (Γ : CosetGraphContext G S P1 P2)
    {d root : Γ.Vertex} (hroot : Γ.adjacent d root)
    (hmodel : QuotientIsFrobenius20 (GAt Γ d) (QAt Γ d)) :
    ((GAt Γ d ⊓ GAt Γ root).subgroupOf (GAt Γ d)).index=5 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ,_,projection,hsurj,hker⟩ := hmodel
  let edge := (GAt Γ d ⊓ GAt Γ root).subgroupOf (GAt Γ d)
  have hkerle : projection.ker≤edge := by
    rw [hker]
    exact subgroupOf_mono _ (coset_neighbor_core_le_edge Γ h7 hroot)
  have hidx : (edge.map projection).index=edge.index := edge.index_map_eq hsurj hkerle
  have hcard : Nat.card (SemidirectProduct C5 C4 φ)=20 := by
    rw [SemidirectProduct.card]
    norm_num [C5,C4]
  have hdvd : edge.index∣20 := by
    rw [←hidx,←hcard]
    exact (edge.map projection).index_dvd_card
  obtain ⟨_,sylow,hsylow⟩ := ((lemma_seven_three h7 Γ).sylow_and_core d root
    ((mem_neighborhood_iff_adjacent Γ).mpr hroot) default).1
  have hsle : (sylow : Subgroup (GAt Γ d))≤edge := by
    intro actor hactor
    have hamb : (actor:G)∈sylowTwoAmbient (GAt Γ d⊓GAt Γ root) default := by
      rw [←hsylow]
      exact mem_map_of_mem _ hactor
    change (actor:G)∈GAt Γ d⊓GAt Γ root
    obtain ⟨edgeActor,_,heq⟩ := hamb
    exact heq ▸ edgeActor.property
  have hodd : ¬2∣edge.index := fun hd =>
    sylow.not_dvd_index (hd.trans (index_dvd_of_le hsle))
  have hone : edge.index≠1 := fun heq =>
    coset_neighbor_edge_proper Γ h7 hroot (edge.index_eq_one.mp heq)
  have hbound := Nat.le_of_dvd (by decide : 0<20) hdvd
  change edge.index=5
  interval_cases edge.index <;> omega

public theorem frobenius_twenty_edge_neighbor_transitivity
    (h7 : SectionSevenHypotheses G S P1 P2) (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) (hmodel : QuotientIsFrobenius20 (GAt Γ d) (QAt Γ d))
    (root left right : Γ.Vertex)
    (hroot : Γ.adjacent d root) (hleft : Γ.adjacent d left) (hright : Γ.adjacent d right)
    (hleftNe : left≠root) (hrightNe : right≠root) :
    ∃ actor : G, actor∈GAt Γ d⊓GAt Γ root ∧ Γ.act actor left=right := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := GAt Γ d
  let Q := QAt Γ d
  let edge := (P⊓GAt Γ root).subgroupOf P
  let X := {neighbor // Γ.adjacent d neighbor}
  let _ : Finite Γ.Vertex := Γ.finiteVertex
  let _ : Finite X := inferInstance
  let _ := coset_neighbor_action Γ d
  let _ := coset_neighbor_action_pretransitive Γ h7 d
  have hdegree : Nat.card X=5 := by
    rw [←MulAction.index_stabilizer_of_transitive P (⟨root,hroot⟩:X),
      coset_neighbor_stabilizer]
    exact edge_index_five h7 Γ hroot hmodel
  obtain ⟨φ,hφ,projection,hsurj,hker⟩ := hmodel
  let M := SemidirectProduct C5 C4 φ
  have hmodelCard : Nat.card M=20 := by
    rw [SemidirectProduct.card]
    norm_num [C5,C4]
  have hQedge : Q≤P⊓GAt Γ root := coset_neighbor_core_le_edge Γ h7 hroot
  have hkerle : projection.ker≤edge := by
    rw [hker]
    exact subgroupOf_mono _ hQedge
  have hidx : (edge.map projection).index=5 :=
    (edge.index_map_eq hsurj hkerle).trans (edge_index_five h7 Γ hroot ⟨φ,hφ,projection,hsurj,hker⟩)
  let A := edge.map projection
  have hAcard : Nat.card A=4 := by
    have hh := A.index_mul_card
    rw [hidx,hmodelCard] at hh
    omega
  have hedgecard : Nat.card (P⊓GAt Γ root : Subgroup G)=4*Nat.card Q := by
    have hgroup := projection.ker.index_mul_card
    rw [index_ker,projection.range_eq_top_of_surjective hsurj,card_top,hker,
      Nat.card_congr (subgroupOfEquivOfLe (hQedge.trans inf_le_left)).toEquiv,
      hmodelCard] at hgroup
    change 20*Nat.card Q=Nat.card P at hgroup
    have hedge := edge.index_mul_card
    rw [edge_index_five h7 Γ hroot ⟨φ,hφ,projection,hsurj,hker⟩,
      Nat.card_congr (subgroupOfEquivOfLe
        (show P⊓GAt Γ root≤P from inf_le_left)).toEquiv] at hedge
    change 5*Nat.card (P⊓GAt Γ root : Subgroup G)=Nat.card P at hedge
    omega
  have hQtwo : IsPGroup 2 Q := by
    change IsPGroup 2 (Γ.twoCoreAt d)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p:=2) (G:=P)).map P.subtype
  have hedgetwo : IsPGroup 2 (P⊓GAt Γ root : Subgroup G) := by
    obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hQtwo
    apply IsPGroup.of_card (n:=n+2)
    rw [hedgecard,hn,pow_add]
    ring
  let representation := MulAction.toPermHom P X
  have hrepresentationKernel : representation.ker=projection.ker := by
    rw [hker]
    ext actor
    change representation actor=1 ↔ (actor:G)∈Q
    have hfix := coset_neighbor_kernel_of_edge_two_group Γ h7 hroot hedgetwo actor⁻¹
    change (actor:G)⁻¹∈Q ↔ ∀ other, Γ.adjacent d other → Γ.act (actor:G)⁻¹ other=other at hfix
    rw [Subgroup.inv_mem_iff] at hfix
    rw [hfix]
    constructor
    · intro heq neighbor hneighbor
      exact congrArg (fun p : Equiv.Perm X => (p ⟨neighbor,hneighbor⟩ : Γ.Vertex)) heq
    · intro heq
      ext neighbor
      exact heq neighbor neighbor.property
  let _ : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p:=2) (by simpa using hAcard)
  have hexists : ∃ a : A, a^2≠1 := by
    by_contra hn
    push Not at hn
    have hel : IsElementaryAbelian 2 A := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hn }
    have hb := SemidirectProduct.elementary_two_subgroup_card_le_two φ A hel
    change Nat.card A≤2 at hb
    rw [hAcard] at hb
    omega
  obtain ⟨a,hasquare⟩ := hexists
  have hafour : a^4=1 := by
    simpa only [hAcard] using (pow_card_eq_one' (x:=a))
  obtain ⟨actor,hactor,himage⟩ := a.property
  let p := representation actor
  have hpfour : p^4=1 := by
    change (representation actor)^4=1
    rw [←map_pow]
    change actor^4∈representation.ker
    rw [hrepresentationKernel]
    change projection (actor^4)=1
    rw [map_pow,himage]
    exact congrArg Subtype.val hafour
  have hpsquare : p^2≠1 := by
    intro heq
    apply hasquare
    apply Subtype.ext
    have hk : actor^2∈representation.ker := by
      change representation (actor^2)=1
      rw [map_pow]
      exact heq
    rw [hrepresentationKernel] at hk
    change projection (actor^2)=1 at hk
    change (a:M)^2=1
    simpa only [map_pow,himage] using hk
  have hproot : p (⟨root,hroot⟩:X)=⟨root,hroot⟩ := by
    have hmem : actor∈MulAction.stabilizer P (⟨root,hroot⟩:X) := by
      rw [coset_neighbor_stabilizer]
      exact hactor
    exact hmem
  obtain ⟨n,hn⟩ := Equiv.Perm.exists_pow_apply_eq_of_order_four_card_five
    hdegree p hpfour hpsquare hproot
    (show (⟨left,hleft⟩:X)≠⟨root,hroot⟩ from fun heq=>hleftNe (congrArg Subtype.val heq))
    (show (⟨right,hright⟩:X)≠⟨root,hroot⟩ from fun heq=>hrightNe (congrArg Subtype.val heq))
  refine ⟨((actor^n.val:P):G)⁻¹,?_,?_⟩
  · exact (P⊓GAt Γ root).inv_mem ((P⊓GAt Γ root).pow_mem hactor n.val)
  · have hpow : p^n.val=representation (actor^n.val) := (map_pow representation actor n.val).symm
    rw [hpow] at hn
    exact congrArg Subtype.val hn
end Stellmacher.SectionNine
