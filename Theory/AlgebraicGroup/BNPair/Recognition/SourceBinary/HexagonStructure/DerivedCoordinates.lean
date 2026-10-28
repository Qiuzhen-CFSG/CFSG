module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi

/-!
# The outside coordinates of a hexagon derived radical

Project the unipotent group U onto U/V_i. The canonical simple root
U_i maps isomorphically onto this quotient, so the first coordinate of
an element of [V_j,V_j] lies in [U_i,U_i]. The literal source reflection
normalizes V_j and exchanges the two outside root factors. Applying the
same projection after reflection puts the final coordinate in the derived
subgroup of U_i^(s_j).

The resulting ordered product bound leaves the full three-middle-root
factor intact. It needs no abelianness, class-two or local model hypothesis.
Its unitary consumer replaces the outside root commutators by their centers
to bound the initial derived configuration; it does not incorrectly place
that whole derived subgroup inside the middle roots.
Source: Fong--Seitz I (3G), pp.14--16, and (6D), p.42.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement

private theorem derived_complement_coordinate {G : Type*} [Group G]
    (U A N : Subgroup G) (hAU : A ≤ U) (hNU : N ≤ U)
    (hN : U ≤ normalizer (N : Set G))
    (hprod : (U : Set G) = (A : Set G) * (N : Set G))
    (hdis : Disjoint A N) (a : A) {b : G} (hb : b ∈ N)
    (hder : (a : G)*b ∈ ⁅U,U⁆) : a ∈ _root_.commutator A := by
  let K := N.subgroupOf U
  let : K.Normal := normal_subgroupOf_of_le_normalizer hN
  let π := QuotientGroup.mk' K
  let f := π.comp (inclusion hAU)
  have hfs : Function.Surjective f := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H z =>
      have hz : (z : G) ∈ (A : Set G) * (N : Set G) := hprod ▸ z.property
      obtain ⟨a,ha,b,hb,hab⟩ := hz
      refine ⟨⟨a,ha⟩,?_⟩
      have he : z = inclusion hAU ⟨a,ha⟩ * (⟨b,hNU hb⟩ : U) := Subtype.ext hab.symm
      change π (inclusion hAU ⟨a,ha⟩) = π z
      rw [he,map_mul,show π (⟨b,hNU hb⟩ : U) = 1 from (QuotientGroup.eq_one_iff _).mpr hb,mul_one]
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hh : π (inclusion hAU x) = 1 := hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff (inclusion hAU x)).mp hh
    exact Subtype.ext (disjoint_def.mp hdis x.property hxN)
  have hmap : (_root_.commutator A).map f = _root_.commutator (U ⧸ K) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hfs,_root_.commutator_def]
  have hderU : (inclusion hAU a * (⟨b,hNU hb⟩ : U)) ∈ _root_.commutator U := by
    have hm : (a : G)*b ∈ (_root_.commutator U).map U.subtype := by
      rwa [map_subtype_commutator]
    obtain ⟨x,hx,he⟩ := hm
    exact (show x = inclusion hAU a * (⟨b,hNU hb⟩ : U) from Subtype.ext he) ▸ hx
  have hπ : π (inclusion hAU a * (⟨b,hNU hb⟩ : U)) ∈ _root_.commutator (U ⧸ K) := by
    have hm := mem_map_of_mem π hderU
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K),
      ←_root_.commutator_def] at hm
    exact hm
  rw [map_mul,show π (⟨b,hNU hb⟩ : U) = 1 from (QuotientGroup.eq_one_iff _).mpr hb,mul_one] at hπ
  have hf : f a ∈ (_root_.commutator A).map f := hmap ▸ hπ
  obtain ⟨x,hx,he⟩ := hf
  exact hfi he ▸ hx

private theorem derived_complement_coordinate_right {G : Type*} [Group G]
    (U A N : Subgroup G) (hAU : A ≤ U) (hNU : N ≤ U)
    (hN : U ≤ normalizer (N : Set G))
    (hprod : (U : Set G) = (A : Set G) * (N : Set G))
    (hdis : Disjoint A N) (a : A) {b : G} (hb : b ∈ N)
    (hder : b*(a : G) ∈ ⁅U,U⁆) : a ∈ _root_.commutator A := by
  let c := (a : G)⁻¹*b*a
  have hc : c ∈ N := by
    have hh := (mem_normalizer_iff.mp (hN (U.inv_mem (hAU a.property))) b).mp hb
    simpa only [inv_inv] using hh
  apply derived_complement_coordinate U A N hAU hNU hN hprod hdis a hc
  simpa only [c,mul_assoc,mul_inv_cancel_left] using hder

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The first outside coordinate of a derived-radical element lies in the
intrinsic derived subgroup of the first root. -/
theorem radical_derived_first_coordinate (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (a : simpleRoot Q split i) (b : middleRoots Q split i j)
    (c : rootAt Q split i (Q.simple j))
    (hx : (a : X ⧸ Q.D)*b*c ∈ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆) :
    a ∈ _root_.commutator (simpleRoot Q split i) := by
  have hcV : (c : X ⧸ Q.D) ∈ simpleRemainder Q split i :=
    middleRoots_le_remainder Q split hm j i hij.symm
      (mem_sup_left (mem_sup_left c.property))
  apply derived_complement_coordinate split.U (simpleRoot Q split i) (simpleRemainder Q split i)
    (simpleRoot_le Q split i) inf_le_left
    (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i hKi)))
    (simpleRoot_mul_remainder Q split i).symm (simpleRoot_disjoint_remainder Q split i) a
    (mul_mem (middleRoots_le_other_remainder Q split hm i j hij b.property) hcV)
  simpa only [mul_assoc] using (commutator_mono inf_le_left inf_le_left hx)

/-- The final outside coordinate of a derived-radical element lies in the
intrinsic derived subgroup of the final root. -/
theorem radical_derived_last_coordinate (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (a : simpleRoot Q split i) (b : middleRoots Q split i j)
    (c : rootAt Q split i (Q.simple j))
    (hx : (a : X ⧸ Q.D)*b*c ∈ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆) :
    c ∈ _root_.commutator (rootAt Q split i (Q.simple j)) := by
  let s := UnitarySource.actorReflection Q split j
  let α := MulAut.conj (s.val : X ⧸ Q.D)
  have hc : α c ∈ simpleRoot Q split i := by
    exact (SetLike.ext_iff.mp (rootAt_eq Q split i (Q.simple j) s.val s.class_eq)
      (c : X ⧸ Q.D)).mp c.property
  have hb : α b ∈ middleRoots Q split i j := by
    have he := middleRoots_conjugate Q split hm i j hij s.val s.class_eq
    have hh : (b : X ⧸ Q.D) ∈ rightConjugate (middleRoots Q split i j) (s.val : X ⧸ Q.D) := he.symm ▸ b.property
    exact hh
  have ha : α a ∈ rootAt Q split i (Q.simple j) := by
    have hs : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s.val⁻¹ = Q.simple j := by
      rw [map_inv,s.class_eq]
      exact inv_eq_of_mul_eq_one_right (by
        simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2)
    rw [rootAt_eq Q split i (Q.simple j) s.val⁻¹ hs]
    change (s.val : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹)*
      ((s.val : X ⧸ Q.D)⁻¹)⁻¹ ∈ simpleRoot Q split i
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using a.property
  have hαx : α ((a : X ⧸ Q.D)*b*c) ∈ ⁅split.U,split.U⁆ := by
    have hn : (s.val : X ⧸ Q.D) ∈ normalizer
        ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set _) := by
      rw [mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split j hKj
          (rankOne_le_parabolic Q split j s.mem_rankOne))]
    exact commutator_mono inf_le_left inf_le_left ((mem_normalizer_iff.mp hn _).mp hx)
  have hader : (⟨α c,hc⟩ : simpleRoot Q split i) ∈ _root_.commutator (simpleRoot Q split i) := by
    apply derived_complement_coordinate_right split.U (simpleRoot Q split i) (simpleRemainder Q split i)
      (simpleRoot_le Q split i) inf_le_left
      (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
        (remainder_parabolic_normalizes Q split i hKi)))
      (simpleRoot_mul_remainder Q split i).symm (simpleRoot_disjoint_remainder Q split i) ⟨α c,hc⟩
      (mul_mem (middleRoots_le_remainder Q split hm j i hij.symm
        (mem_sup_left (mem_sup_left ha)))
        (middleRoots_le_other_remainder Q split hm i j hij hb))
    simpa only [map_mul] using hαx
  let f : rootAt Q split i (Q.simple j) →* simpleRoot Q split i :=
    (α.toMonoidHom.comp (rootAt Q split i (Q.simple j)).subtype).codRestrict _ (by
      intro x
      exact (SetLike.ext_iff.mp (rootAt_eq Q split i (Q.simple j) s.val s.class_eq)
        (x : X ⧸ Q.D)).mp x.property)
  have hfi : Function.Injective f := fun x y he => Subtype.ext (α.injective (congrArg Subtype.val he))
  have hfs : Function.Surjective f := by
    intro y
    refine ⟨⟨α.symm y,?_⟩,?_⟩
    · rw [rootAt_eq Q split i (Q.simple j) s.val s.class_eq]
      change α (α.symm y) ∈ simpleRoot Q split i
      simpa only [α.apply_symm_apply] using y.property
    · exact Subtype.ext (α.apply_symm_apply y)
  have hmap : (_root_.commutator (rootAt Q split i (Q.simple j))).map f =
      _root_.commutator (simpleRoot Q split i) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hfs,_root_.commutator_def]
  have hh : f c ∈ (_root_.commutator (rootAt Q split i (Q.simple j))).map f := hmap ▸ hader
  obtain ⟨z,hz,he⟩ := hh
  exact hfi he ▸ hz

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Projecting onto both outside root factors bounds the actual derived
radical by their intrinsic derived subgroups and the three middle roots.
No abelianness or class-two premise is needed. -/
theorem radical_derived_coordinates (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
      ((⁅simpleRoot Q split i,simpleRoot Q split i⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) *
        (middleRoots Q split i j : Set (X ⧸ Q.D)) *
      ((⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j)⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  intro x hx
  have hxV : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := commutator_le_self _ hx
  rw [radical_five_product Q split hm i j hij] at hxV
  obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,f,hf,rfl⟩ := hxV
  have hmiddle : b*c*d ∈ middleRoots Q split i j :=
    mul_mem (mul_mem (mem_sup_left (mem_sup_left hb)) (mem_sup_left (mem_sup_right hc)))
      (mem_sup_right hd)
  have hder : a*(b*c*d)*f ∈ ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
    simpa only [SetLike.mem_coe,mul_assoc] using hx
  have haD := radical_derived_first_coordinate Q split hm i j hij hKi ⟨a,ha⟩ ⟨b*c*d,hmiddle⟩ ⟨f,hf⟩ hder
  have hfD := radical_derived_last_coordinate Q split hm i j hij hKi hKj ⟨a,ha⟩ ⟨b*c*d,hmiddle⟩ ⟨f,hf⟩ hder
  have ha' : a ∈ ⁅simpleRoot Q split i,simpleRoot Q split i⁆ := by
    rw [←map_subtype_commutator]
    exact mem_map_of_mem _ haD
  have hf' : f ∈ ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j)⁆ := by
    rw [←map_subtype_commutator]
    exact mem_map_of_mem _ hfD
  exact ⟨a*(b*c*d),⟨a,ha',b*c*d,hmiddle,rfl⟩,f,hf',by simp only [mul_assoc]⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
