module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryPanelDefect
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.ProfileActors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.SpecificGroups.GL2.ThreeResidualImages.QuaternionCore
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The full exceptional affine panel and its Cartan kernel

Suppose the local root closure has a solvable action of order 144 on its
nine-point panel. The whole marked endpoint is solvable: its kernel lies
in the solvable Borel, and the full Cartan supplements the local closure.
The unipotent image is a normal subgroup of order sixteen in the full
point stabilizer. A regular normal ternary plane embeds this stabilizer
in GL₂(3). A larger stabilizer would be all of GL₂(3), whose two-core has
order eight, contradicting the normal sixteen. Thus the entire endpoint
image is precisely the previously identified local group of order 144.

The odd Cartan maps into a stabilizer of order sixteen, so it lies in the
full panel kernel. The exact Cartan/kernel theorem then makes it centralize
the smaller root-generated group. In particular every root-generated simple
reflection fixes this Cartan pointwise. These statements require neither
(2B), perfectness, nor a specified Weyl order, and preserve the actual maps.

Source: Fong--Seitz I, (2A)(VI), pp.8--9, and the beginning of the proof of
(5I), p.31. The binary source catalogue has already reduced the Mersenne
exception to degree nine. BinaryAffineCartan applies the result to the
original full endpoint, its full Borel and the literal Chapter 12 pair.
The later global module argument excluding this alternative is still needed.
-/

public noncomputable section
open Subgroup MulAction Matrix
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

private theorem normal_sixteen_forces_order_sixteen
    {C : Type*} [Group C] [Finite C]
    (f : C →* GL (Fin 2) (ZMod 3)) (hf : Function.Injective f)
    (N : Subgroup C) [N.Normal] (hn : Nat.card N = 16) : Nat.card C = 16 := by
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by rw [card_GL_field]; decide
  have hd : Nat.card C ∣ 48 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    rw [← hGL]
    exact f.range.card_subgroup_dvd_card
  have hd16 : 16 ∣ Nat.card C := hn ▸ N.card_subgroup_dvd_card
  obtain ⟨k,hk⟩ := hd16
  have hk3 : k ∣ 3 := by
    rw [hk] at hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 16)).mp hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h1 | h3
  · simpa only [h1,mul_one] using hk
  · have hc : Nat.card C = 48 := by omega
    have hr : f.range = ⊤ := eq_top_of_card_eq _ (by
      rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,hc,card_GL_field]; decide)
    let e := MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp hr⟩
    let a := e.trans (Subgroup.topEquiv : (⊤ : Subgroup (GL (Fin 2) (ZMod 3))) ≃* _).symm
    let N' := N.map a.toMonoidHom
    let : N'.Normal := Subgroup.Normal.map inferInstance _ a.surjective
    have hN : IsPGroup 2 N' := (IsPGroup.of_card (p := 2) (n := 4) hn).map a.toMonoidHom
    have hle := GeneralLinearGroup.three_normal_two_le_quaternion ⊤ le_top N' hN
    have hcard : Nat.card (N'.map (⊤ : Subgroup (GL (Fin 2) (ZMod 3))).subtype) = 16 := by
      rw [card_map_of_injective (Subgroup.subtype_injective _),
        card_map_of_injective a.injective,hn]
    have hh := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [hcard,GeneralLinearGroup.threeQuaternion_card] at hh
    omega

/-- A normal sixteen in the stabilizer of a solvable nine-point action is the full stabilizer. -/
theorem stabilizer_card_of_normal_sixteen
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    [FaithfulSMul G Ω] [Finite Ω] [Group.IsSolvable G]
    (ht : IsMultiplyPretransitive G Ω 2) (hc : Nat.card Ω = 9)
    (o : Ω) (N : Subgroup (stabilizer G o)) [N.Normal]
    (hn : Nat.card N = 16) : Nat.card (stabilizer G o) = 16 := by
  obtain ⟨A,hAn,hAe,hAcard,hreg⟩ := regular_nine_of_solvable ht hc o
  let := hAn
  let := hAe
  obtain ⟨c,e,he⟩ := GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates
    (show Nat.card A = 3^2 by simpa using hAcard)
  let f := e.toMonoidHom.comp
    ((MulAut.conjNormal : G →* MulAut A).comp (stabilizer G o).subtype)
  exact normal_sixteen_forces_order_sixteen f
    (e.injective.comp (stabilizer_action_injective A o hreg)) N hn

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- Solvability of the faithful local image implies solvability of the whole marked endpoint. -/
theorem endpoint_solvable_of_local_solvable
    (hs : Group.IsSolvable (localGroup Q split i)) :
    Group.IsSolvable (Q.tits.standardParabolic {Q.simple i}) := by
  let H := Q.tits.B ⊓ Q.tits.N
  let := split.isTwo.isNilpotent
  let := split.abelian
  have hb : Group.IsSolvable Q.tits.B := by
    rw [← split.factorization]
    exact Group.isSolvable_sup_of_normalizes _ _ (inf_le_left.trans split.normalizes)
  let := hb
  let K := (localAction Q split i).ker
  let k : K →* Q.tits.B :=
    ((localClosure Q split i).subtype.comp K.subtype).codRestrict Q.tits.B
      (fun x => localKernel_le_borel Q i ((localAction_ker Q split i).le x.property))
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (f := k)
    (fun x y he => Subtype.ext (Subtype.ext (show x.val.val = y.val.val from congrArg (fun z : Q.tits.B => z.val) he)))
  let : Group.IsSolvable (localAction Q split i).range := hs
  have hc : Group.IsSolvable (localClosure Q split i) :=
    Group.isSolvable_of_ker_le_range K.subtype (localAction Q split i).rangeRestrict
      (by rw [range_subtype,MonoidHom.ker_rangeRestrict])
  let := hc
  rw [← localClosure_sup_torus Q split i (actorReflection Q split i)]
  exact Group.isSolvable_sup_of_normalizes _ _
    ((inf_le_left.trans (Q.tits.B_le_standardParabolic _)).trans
      (localClosure_parabolic_normalizes Q split i (actorReflection Q split i)))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource BinaryPanel
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The whole endpoint action has no odd enlargement in the exceptional affine case. -/
theorem endpoint_image_card_of_affine
    (hs : Group.IsSolvable (localGroup Q split i))
    (hp : Nat.card (Panel Q i) = 9) (hg : Nat.card (localGroup Q split i) = 144) :
    Nat.card (endpointAction Q i).range = 144 ∧
      Nat.card (stabilizer (endpointAction Q i).range (panelBase Q i)) = 16 := by
  let E := Q.tits.standardParabolic {Q.simple i}
  let M := (endpointAction Q i).range
  let f := (endpointAction Q i).rangeRestrict
  let C := stabilizer M (panelBase Q i)
  let U := split.U.subgroupOf E
  let B := Q.tits.B.subgroupOf E
  let V := U.map f
  have hf : Function.Surjective f := (endpointAction Q i).rangeRestrict_surjective
  have hCB : C.comap f = B := by
    ext x
    change endpointAction Q i x (panelBase Q i) = panelBase Q i ↔ (x : X ⧸ Q.D) ∈ Q.tits.B
    rw [ReeSource.panelBase_eq_mk_one Q split i]
    change QuotientGroup.mk (x * 1) = (QuotientGroup.mk 1 : Panel Q i) ↔ _
    rw [QuotientGroup.eq]
    simp only [mul_one,inv_mem_iff]
    rfl
  have hBC : B.map f = C := by rw [← hCB,map_comap_eq_self_of_surjective hf]
  have hUC : V ≤ C := hBC ▸ map_mono (subgroupOf_mono E split.U_le)
  have hBU : B ≤ normalizer (U : Set E) := by
    intro b hb
    exact (le_normalizer_comap E.subtype) (split.normalizes hb)
  have hCV : C ≤ normalizer (V : Set M) := by
    rw [← hBC]
    exact (map_mono hBU).trans (U.le_normalizer_map f)
  let N := V.subgroupOf C
  let : N.Normal := normal_subgroupOf_of_le_normalizer hCV
  have hVcard : Nat.card V = 16 := by
    have hk : f.ker = (localKernel Q i).subgroupOf E := by
      rw [MonoidHom.ker_rangeRestrict]
      rw [localKernel_subgroupOf,normalCore_eq_ker]
      rfl
    rw [← relIndex_ker,hk,relIndex_subgroupOf
      (show split.U ≤ E from split.U_le.trans (Q.tits.B_le_standardParabolic _))]
    rw [← inf_relIndex_left split.U (localKernel Q i)]
    change (LocalCover.radical Q split i).relIndex split.U = 16
    rw [← localSylow_card]
    rw [(localSylow Q split i).card_eq_multiplicity,hg]
    decide +kernel
  have hNcard : Nat.card N = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv).trans hVcard
  let := endpoint_solvable_of_local_solvable Q split i hs
  let : Group.IsSolvable M := Group.isSolvable_of_surjective hf
  have hLM : localGroup Q split i ≤ M := by
    change (localAction Q split i).range ≤ _
    rw [localAction_eq_panelAction,panelAction]
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion (localClosure_le_parabolic Q split i) x,rfl⟩
  have ht : IsMultiplyPretransitive M (Panel Q i) 2 := by
    apply is_two_pretransitive_iff.mpr
    intro a b c d hab hcd
    obtain ⟨g,hg,hg'⟩ := is_two_pretransitive_iff.mp
      (localGroup_two_pretransitive Q split i) hab hcd
    exact ⟨⟨g,hLM g.property⟩,hg,hg'⟩
  have hCcard := stabilizer_card_of_normal_sixteen ht hp (panelBase Q i) N hNcard
  have hMcard : Nat.card M = 144 := by
    let : IsPreprimitive M (Panel Q i) := isPreprimitive_of_is_two_pretransitive ht
    have he := C.index_mul_card
    rw [index_stabilizer_of_transitive,hp,hCcard] at he
    omega
  exact ⟨hMcard,hCcard⟩

/-- The entire odd Cartan lies in the full endpoint permutation kernel. -/
theorem torus_le_kernel_of_affine
    (hs : Group.IsSolvable (localGroup Q split i))
    (hp : Nat.card (Panel Q i) = 9) (hg : Nat.card (localGroup Q split i) = 144) :
    Q.tits.B ⊓ Q.tits.N ≤ localKernel Q i := by
  let E := Q.tits.standardParabolic {Q.simple i}
  let M := (endpointAction Q i).range
  let C := stabilizer M (panelBase Q i)
  have hC := (endpoint_image_card_of_affine Q split i hs hp hg).2
  intro t ht
  let a : E := ⟨t,Q.tits.B_le_standardParabolic _ ht.1⟩
  let b : M := (endpointAction Q i).rangeRestrict a
  have hb : b ∈ C := by
    change endpointAction Q i a (panelBase Q i) = panelBase Q i
    rw [ReeSource.panelBase_eq_mk_one Q split i]
    change QuotientGroup.mk (a*1) = (QuotientGroup.mk 1 : Panel Q i)
    rw [QuotientGroup.eq]
    simpa only [mul_one,inv_mem_iff] using (show a ∈ Q.tits.B.subgroupOf E from ht.1)
  let c : C := ⟨b,hb⟩
  have hc16 : c^16 = 1 := hC ▸ (pow_card_eq_one' (x := c))
  have hct : c^(Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) = 1 := by
    have htq := pow_card_eq_one' (x := (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N)))
    apply Subtype.ext
    apply Subtype.ext
    change (endpointAction Q i a)^_ = 1
    rw [← map_pow]
    rw [show a^Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = 1 from
      Subtype.ext (show t^Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = 1 from
        congrArg (fun z : ↥(Q.tits.B ⊓ Q.tits.N) => z.val) htq),map_one]
  have he : c = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (split.odd.pow_left 4)
      (orderOf_dvd_of_pow_eq_one hc16) (orderOf_dvd_of_pow_eq_one hct))
  have ha : a ∈ (endpointAction Q i).ker := congrArg (fun z : C => z.val.val) he
  refine ⟨a,?_,rfl⟩
  rwa [normalCore_eq_ker]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The exceptional local group is the whole faithful endpoint image. -/
theorem endpoint_image_eq_localGroup_of_affine
    (hs : Group.IsSolvable (localGroup Q split i))
    (hp : Nat.card (Panel Q i) = 9) (hg : Nat.card (localGroup Q split i) = 144) :
    (endpointAction Q i).range = localGroup Q split i := by
  symm
  apply eq_of_le_of_card_ge
  · change (localAction Q split i).range ≤ _
    rw [localAction_eq_panelAction,panelAction]
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion (localClosure_le_parabolic Q split i) x,rfl⟩
  · rw [hg,(endpoint_image_card_of_affine Q split i hs hp hg).1]

/-- The actual whole Cartan centralizes the smaller root-generated group. -/
theorem torus_centralizes_rankOne_of_affine
    (hs : Group.IsSolvable (localGroup Q split i))
    (hp : Nat.card (Panel Q i) = 9) (hg : Nat.card (localGroup Q split i) = 144) :
    Q.tits.B ⊓ Q.tits.N ≤ centralizer (rankOne Q split i : Set (X ⧸ Q.D)) := by
  intro t ht
  have hk : t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ ReeSource.embeddedPanelKernel Q i :=
    ⟨ht,torus_le_kernel_of_affine Q split i hs hp hg ht⟩
  rw [← ReeSource.cartan_centralizer_rankOneRootGroup Q split i] at hk
  exact hk.2

/-- Every root-generated simple lift fixes this Cartan pointwise. -/
theorem affine_reflection_commutes_torus
    (hs : Group.IsSolvable (localGroup Q split i))
    (hp : Nat.card (Panel Q i) = 9) (hg : Nat.card (localGroup Q split i) = 144)
    (s : RootReflection Q split i) (t : ↥(Q.tits.B ⊓ Q.tits.N)) :
    (s.val : X ⧸ Q.D) * t = (t : X ⧸ Q.D) * s.val :=
  mem_centralizer_iff.mp (torus_centralizes_rankOne_of_affine Q split i hs hp hg t.property)
    _ s.mem_rankOne

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
