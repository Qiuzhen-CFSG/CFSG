module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.MarkedReflection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanBraid

/-!
# Cartan reflections and the braid on the synchronized U₅ source

The aligned SL₂ pinning identifies the linear reflection commutator from
its simple-root weight. For the unitary reflection, the natural outer
axes identify the whole Cartan intersection with the original SU₃ torus;
its A and C weights then determine the reflection commutator exactly.
This gives both coordinate formulas for the constructed full Cartan.

The fourth power of the two marked reflections lies in the odd Cartan.
Both reflections invert it, so it lies in the linear rank-one factor.
Conjugating its action on D by the unitary reflection, which fixes all of
D, forces the linear torus parameter to equal its inverse, hence to be
one in characteristic two. The full source root groups, their centers,
and fields of orders two and four are retained throughout.

The final theorem supplies exactly the three Cartan--Weyl clauses consumed
by PresentationEquations and the native source construction. Its positive
relations and root weights are those proved on the same source witnesses;
no surjectivity of the full Cartan parametrization is used.
Source: Fong--Seitz II (8C), pp.203–210, especially (8.24)–(8.37).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative Pointwise
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.PSL2.SemilinearCoverage
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
section Linear
variable {X K : Type*} [Group X] [Field K] [Finite K] [CharP K 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,K)) (s : RootReflection Q split i)
/-- A Cartan element fixing the unit simple-root element commutes with its
specified source reflection. This includes the binary rank-one group. -/
private theorem linear_cartan_commutes_reflection_of_fixes_one {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (hu : t * alignedSimpleParameter Q split i hVi μ s (.ofAdd 1) * t⁻¹ =
      alignedSimpleParameter Q split i hVi μ s (.ofAdd 1)) :
    Commute t (s.val : X ⧸ Q.D) := by
  let w : X ⧸ Q.D := s.val
  let f := alignedPinningHom Q split i hVi μ s
  let c := t*w*t⁻¹*w⁻¹
  have hcR : c ∈ rankOne Q split i :=
    (rankOne Q split i).mul_mem
      ((mem_normalizer_iff.mp (rankOne_torus_normalizes Q split i ht) w).mp s.mem_rankOne)
      ((rankOne Q split i).inv_mem s.mem_rankOne)
  have hnH : w ∈ normalizer (Q.tits.B ⊓ Q.tits.N : Set (X ⧸ Q.D)) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mp Q.tits.intersection_normal s.val.property
  have hcH : c ∈ Q.tits.B ⊓ Q.tits.N := by
    change t*w*t⁻¹*w⁻¹ ∈ _
    rw [mul_assoc t w t⁻¹, mul_assoc]
    exact (Q.tits.B ⊓ Q.tits.N).mul_mem ht
      ((mem_normalizer_iff.mp hnH t⁻¹).mp ((Q.tits.B ⊓ Q.tits.N).inv_mem ht))
  obtain ⟨b,hb⟩ := exists_alignedTorus_of_mem Q split i hVi μ s hcH hcR
  have hw : MulAut.conj t w = f (tor b * weyl K) := by
    rw [map_mul]
    change t*w*t⁻¹ = alignedTorus Q split i hVi μ s b * f (weyl K)
    rw [hb,alignedPinningHom_weyl]
    change t*w*t⁻¹ = (t*w*t⁻¹*w⁻¹)*w
    group
  have hword := aligned_rankOne_word Q split i hVi μ s (1 : Kˣ)
  have he := congrArg (MulAut.conj t) hword
  change MulAut.conj t (f (uni 1) * (w*f (uni 1)*w⁻¹) * f (uni 1)) =
    MulAut.conj t (f (tor 1)*w) at he
  have hu' : MulAut.conj t (f (uni 1)) = f (uni 1) := hu
  simp only [map_mul,map_inv,hu',hw] at he
  have ht1 : tor (1 : Kˣ) = 1 := by ext j k; fin_cases j <;> fin_cases k <;> simp
  rw [ht1,map_one,map_one,one_mul] at he
  have hm := (alignedPinningHom_injective Q split i hVi μ s)
    (show f (uni 1 * ((tor b*weyl K)*uni 1*(tor b*weyl K)⁻¹)*uni 1) = f (tor b*weyl K) by
      simpa only [map_mul,map_inv] using he)
  have hentry := congrArg (fun g : SL2 K => g.val 0 0) hm
  have hb2 : (b : K)⁻¹^2 = 1 := by
    have hh : 1 + (b : K)⁻¹ * (b : K)⁻¹ = 0 := by
      simpa [Matrix.mul_apply,Fin.sum_univ_two,CharTwo.neg_eq] using hentry
    simpa only [pow_two] using (CharTwo.add_eq_zero.mp hh).symm
  have hb1 : b = 1 := by
    apply Units.ext
    have hi : (b : K)⁻¹ = 1 := CharTwo.sq_injective (hb2.trans (one_pow 2).symm)
    simpa only [inv_inv,inv_one,Units.val_one] using congrArg Inv.inv hi
  have hw' : MulAut.conj t w = w := by
    rw [hw,hb1,ht1,one_mul]
    exact alignedPinningHom_weyl Q split i hVi μ s
  exact (mul_inv_eq_iff_eq_mul.mp hw')


/-- The rank-one scalar on the unit root determines the Cartan-reflection
commutator in the same aligned pinning. -/
private theorem linear_reflection_cartan_of_weight {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N) (a : Kˣ)
    (hu : t * alignedSimpleParameter Q split i hVi μ s (.ofAdd 1) * t⁻¹ =
      alignedSimpleParameter Q split i hVi μ s (.ofAdd (a : K))) :
    s.val * t * (s.val : X ⧸ Q.D)⁻¹ =
      t * alignedTorusHom Q split i hVi μ s a⁻¹ := by
  have hinj : Function.Injective (fun b : Kˣ => b^2) := by
    intro b c he
    apply Units.ext
    apply CharTwo.sq_injective
    exact congrArg Units.val he
  obtain ⟨b,hb⟩ := (Finite.surjective_of_injective hinj) a
  change b^2 = a at hb
  let T := alignedTorusHom Q split i hVi μ s
  let w : X ⧸ Q.D := s.val
  have hbK : (b : K)^2 = (a : K) := congrArg Units.val hb
  have hcH : T b⁻¹ * t ∈ Q.tits.B ⊓ Q.tits.N :=
    (Q.tits.B ⊓ Q.tits.N).mul_mem (alignedTorus_mem_cartan Q split i hVi μ s b⁻¹) ht
  have hcu : (T b⁻¹ * t) * alignedSimpleParameter Q split i hVi μ s (.ofAdd 1) *
      (T b⁻¹ * t)⁻¹ = alignedSimpleParameter Q split i hVi μ s (.ofAdd 1) := by
    have he := alignedTorus_root Q split i hVi μ s b⁻¹ (a : K)
    have ha : (↑b⁻¹ : K)^2 * (a : K) = 1 := by
      rw [Units.val_inv_eq_inv_val,← hbK,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ b.ne_zero)]
    rw [ha] at he
    calc
      _ = T b⁻¹ * (t * alignedSimpleParameter Q split i hVi μ s (.ofAdd 1) * t⁻¹) *
          (T b⁻¹)⁻¹ := by group
      _ = _ := by rw [hu]; exact he
  have hc := linear_cartan_commutes_reflection_of_fixes_one Q split i hVi μ s hcH hcu
  have hw : T b * (w*t*w⁻¹) = T b⁻¹*t := by
    have he : w*(T b⁻¹*t)*w⁻¹ = T b⁻¹*t := by
      rw [← hc.eq,mul_assoc,mul_inv_cancel,mul_one]
    have hh := reflection_alignedTorus Q split i hVi μ s b⁻¹
    simp only [inv_inv] at hh
    change w*T b⁻¹*w⁻¹ = T b at hh
    calc
      _ = (w*T b⁻¹*w⁻¹)*(w*t*w⁻¹) := by rw [hh]
      _ = _ := by simpa only [mul_assoc,inv_mul_cancel_left] using he
  calc
    w*t*w⁻¹ = T b⁻¹ * (T b * (w*t*w⁻¹)) := by
      rw [← mul_assoc,← map_mul,inv_mul_cancel,map_one,one_mul]
    _ = T b⁻¹ * (T b⁻¹*t) := by rw [hw]
    _ = T a⁻¹ * t := by rw [← mul_assoc,← map_mul,← pow_two,inv_pow,hb]
    _ = t * T a⁻¹ := by
      let := split.abelian
      exact congrArg Subtype.val (mul_comm
        (⟨_,alignedTorus_mem_cartan Q split i hVi μ s a⁻¹⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
        (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N)))

end Linear


section Braid
variable {X E K : Type*} [Group X] [Field E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j) (ξ : E ≃+* K)
  (t : RootReflection Q split j)
  (hm : rotationOrder Q = 4)
  (ht : (t.val : X ⧸ Q.D)*(t.val : X ⧸ Q.D)=1)
  (htD : ∀ p : hermitianUnipotentCoord J,
    (t.val : X ⧸ Q.D)*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*t.val =
      (reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D))
  (hfirst : ∀ x : E, ∃ p : hermitianUnipotentCoord J, p.val.1=x)
  (hlinD : ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
    let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    H*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*H⁻¹ =
      reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) (u:E) p))

include hij hm ht htD hfirst hlinD in
private theorem source_braid_of_unitary_fixed :
    ((s.val : X ⧸ Q.D)*(t.val : X ⧸ Q.D))^4=1 := by
  let z : Q.tits.N := (s.val*t.val)^4
  have hz : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) z=1 := by
    simp only [z,map_pow,map_mul,s.class_eq,t.class_eq]
    have ho : orderOf (Q.simple i*Q.simple j)=4 := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hm
      · simpa [rotationOrder] using (SemiconjBy.orderOf_eq (Q.simple 0) (show
          SemiconjBy (Q.simple 0) (Q.simple 1*Q.simple 0) (Q.simple 0*Q.simple 1) from
            (mul_assoc _ _ _).symm)).trans hm
      · exact (hij rfl).elim
    rw [←ho]
    exact pow_orderOf_eq_one _
  have hzH : (z : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := (QuotientGroup.eq_one_iff z).mp hz
  have hs := sourceReflection_sq Q split i hVi μ s
  have hsi : (s.val : X ⧸ Q.D)⁻¹=s.val := inv_eq_of_mul_eq_one_right hs
  have hti : (t.val : X ⧸ Q.D)⁻¹=t.val := inv_eq_of_mul_eq_one_right ht
  have hsprod : MulAut.conj (s.val : X ⧸ Q.D) (s.val*t.val)=((s.val : X ⧸ Q.D)*t.val)⁻¹ := by
    change (s.val : X ⧸ Q.D)*(s.val*t.val)*(s.val : X ⧸ Q.D)⁻¹=((s.val : X ⧸ Q.D)*t.val)⁻¹
    rw [←mul_assoc (s.val : X ⧸ Q.D) s.val t.val,hs,one_mul,mul_inv_rev,hti]
  have htprod : MulAut.conj (t.val : X ⧸ Q.D) (s.val*t.val)=((s.val : X ⧸ Q.D)*t.val)⁻¹ := by
    change (t.val : X ⧸ Q.D)*(s.val*t.val)*(t.val : X ⧸ Q.D)⁻¹=((s.val : X ⧸ Q.D)*t.val)⁻¹
    simp only [mul_assoc,mul_inv_rev,hsi,hti,ht,mul_one]
  have hsz : MulAut.conj (s.val : X ⧸ Q.D) (z : X ⧸ Q.D)=(z : X ⧸ Q.D)⁻¹ := by
    change MulAut.conj (s.val : X ⧸ Q.D) (((s.val : X ⧸ Q.D)*t.val)^4)=(((s.val : X ⧸ Q.D)*t.val)^4)⁻¹
    rw [map_pow,hsprod,inv_pow]
  have htz : MulAut.conj (t.val : X ⧸ Q.D) (z : X ⧸ Q.D)=(z : X ⧸ Q.D)⁻¹ := by
    change MulAut.conj (t.val : X ⧸ Q.D) (((s.val : X ⧸ Q.D)*t.val)^4)=(((s.val : X ⧸ Q.D)*t.val)^4)⁻¹
    rw [map_pow,htprod,inv_pow]
  have hzR := cartan_inverted_mem_rankOne Q split i s hzH hsz
  obtain ⟨u,hu⟩ := exists_alignedTorus_of_mem Q split i hVi μ s hzH hzR
  let a : Eˣ := Units.map ξ.symm.toMonoidHom u
  have hau : Units.map ξ.toMonoidHom a=u := by
    apply Units.ext
    exact ξ.apply_symm_apply u
  have hza : alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom a)=(z : X ⧸ Q.D) := by
    rw [hau]
    exact hu
  have htDf (p : hermitianUnipotentCoord J) :
      MulAut.conj (t.val : X ⧸ Q.D) (reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D) =
        reflectedUnitaryChart Q split i j s b p := by
    simpa only [MulAut.conj_apply,hti] using htD p
  obtain ⟨p,hp⟩ := hfirst 1
  have he := congrArg (MulAut.conj (t.val : X ⧸ Q.D)) (hlinD a p)
  rw [hza] at he
  simp only [map_mul,map_inv,htz,htDf,inv_inv] at he
  erw [htDf] at he
  have hi := hlinD a⁻¹ p
  dsimp only at hi
  have hzi : alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom a⁻¹)=(z : X ⧸ Q.D)⁻¹ := by
    change alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom a⁻¹)=_
    rw [map_inv,map_inv]
    exact congrArg Inv.inv hza
  rw [hzi,inv_inv] at hi
  have heq := (reflectedUnitaryChart Q split i j s b).injective
    (Subtype.ext (he.symm.trans hi))
  have haa : (a:E)=(a:E)⁻¹ := by
    have hf := congrArg (fun x : hermitianUnipotentCoord J => x.val.1) heq
    simpa [FivePositive.normParameter,hp] using hf
  have ha1 : a=1 := by
    apply Units.ext
    apply CharTwo.sq_injective
    change (a:E)^2=(1:E)^2
    calc
      (a:E)^2 = (a:E)⁻¹*(a:E) := by rw [pow_two,←haa]
      _ = (1:E)^2 := by rw [inv_mul_cancel₀ a.ne_zero,one_pow]
  have hz1 : (z : X ⧸ Q.D)=1 := by
    rw [←hza,ha1,map_one]
    exact (alignedTorusHom Q split i hVi μ s).map_one
  exact hz1
end Braid

section Source
variable {X E K : Type*} [Group X] [Field E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) E]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (ξ : E ≃+* K) (k : E) (hk : k ≠ 0)
local notation "A" => fun a : E => alignedSimpleParameter Q split i hVi μ s (Multiplicative.ofAdd (ξ a))
variable (hA : ∀ a : E, (naturalSectionMap Q split j c
  (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])
  (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (hC : ∀ a : E, (naturalSectionMap Q split j c (inclusion (opposite_roots_le_remainder Q split i j hij).2
    (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0])
  (t : RootReflection Q split j)
local notation "H" => fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA
local notation "W" => unitaryWeyl Q split j J hJ θ
local notation "U" => unitaryTorus Q split j J hJ θ
local notation "R" => synchronizedRoots Q split i j hVi s μ J b γ ξ

include hb hc hk hA hC t in
omit [CharP E 2] in
/-- The full Cartan intersection with the unitary rank-one actor is exactly
its diagonal torus, with the given natural section retained. -/
theorem exists_unitaryTorus_of_mem {z : X ⧸ Q.D}
    (hzH : z ∈ Q.tits.B ⊓ Q.tits.N) (hzR : z ∈ rankOne Q split j) :
    ∃ u : Eˣ, z=U u := by
  let w := unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw : (w.val : X ⧸ Q.D)=W :=
    unitaryReflection_val Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  let zn : Q.tits.N := ⟨z,hzH.2⟩
  let n : RootReflection Q split j := {
    val := zn*w.val
    class_eq := by
      have he : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) zn=1 :=
        (QuotientGroup.eq_one_iff zn).mpr hzH
      rw [map_mul,he,one_mul,w.class_eq]
    mem_rankOne := (rankOne Q split j).mul_mem hzR w.mem_rankOne }
  obtain ⟨u,hu⟩ := unitaryWeyl_source_factor Q split i j hij hVi hVj s μ J hJ θ c hc ξ k hk hA γ hC n
  change z*(w.val : X ⧸ Q.D)=U u*W at hu
  rw [hw] at hu
  exact ⟨u,mul_right_cancel hu⟩

variable (hHA : ∀ p a, (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*(synchronizedRoots Q split i j hVi s μ J b γ ξ).A (.ofAdd a)*((fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p)⁻¹ =
      (synchronizedRoots Q split i j hVi s μ J b γ ξ).A (.ofAdd (((p.1:E)/(p.2:E))*a)))
  (hHC : ∀ p a, (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*(synchronizedRoots Q split i j hVi s μ J b γ ξ).C (.ofAdd a)*((fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p)⁻¹ =
      (synchronizedRoots Q split i j hVi s μ J b γ ξ).C (.ofAdd (((p.1:E)*J.conj (p.2:E))*a)))

include hb hc hk hA hHA in
omit [CharP E 2] in
/-- The linear reflection swaps the two exact Cartan coordinates. -/
theorem fullUnitaryCartan_linear_reflection (p : Eˣ × Eˣ) :
    (s.val : X ⧸ Q.D)*H p*s.val=H (p.2,p.1) := by
  have hw := sourceReflection_sq Q split i hVi μ s
  have hwi : (s.val : X ⧸ Q.D)⁻¹=s.val := inv_eq_of_mul_eq_one_right hw
  have hu := hHA p 1
  change H p*A 1*(H p)⁻¹=A (((p.1:E)/(p.2:E))*1) at hu
  simp only [map_one,mul_one] at hu
  have he := linear_reflection_cartan_of_weight Q split i hVi μ s
    (fullUnitaryCartan_mem Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA p)
    (Units.map ξ.toMonoidHom (p.1/p.2))
    (by
      rw [Units.coe_map,Units.val_div_eq_div_val]
      exact hu)
  rw [hwi] at he
  rw [he]
  let T := alignedTorusHom Q split i hVi μ s
  have hp : unitaryCartanParameter J (p.2,p.1)=unitaryCartanParameter J p := by
    simp only [unitaryCartanParameter,MonoidHom.coe_mk,OneHom.coe_mk,mul_comm p.1 p.2]
  change (T (Units.map ξ.toMonoidHom p.1)*U (unitaryCartanParameter J p))*
    T (Units.map ξ.toMonoidHom (p.1/p.2))⁻¹ =
      T (Units.map ξ.toMonoidHom p.2)*U (unitaryCartanParameter J (p.2,p.1))
  have hcom : Commute (U (unitaryCartanParameter J p))
      (T (Units.map ξ.toMonoidHom (p.1/p.2))⁻¹) := by
    let := split.abelian
    exact congrArg Subtype.val (mul_comm
      (⟨_,unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA _⟩ :
        ↥(Q.tits.B ⊓ Q.tits.N))
      (⟨_,alignedTorus_mem_cartan Q split i hVi μ s _⟩ : ↥(Q.tits.B ⊓ Q.tits.N)))
  rw [hp,mul_assoc,hcom.eq,←mul_assoc,←map_mul,←map_inv,←map_mul]
  congr 2
  congr 1
  simp [div_eq_mul_inv]

include hb hc hk hA hC t hHA hHC in
omit [CharP E 2] in
/-- The unitary reflection applies inverse conjugation to the second exact
Cartan coordinate, including all scalar elements in the SU₃ actor. -/
theorem fullUnitaryCartan_unitary_reflection (p : Eˣ × Eˣ) :
    W*H p*W=H (p.1,(Units.map J.conj.toMonoidHom p.2)⁻¹) := by
  let w := unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw : (w.val : X ⧸ Q.D)=W :=
    unitaryReflection_val Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw2 : W*W=1 := unitaryWeyl_square Q split j J hJ θ
  have hwi : W⁻¹=W := inv_eq_of_mul_eq_one_right hw2
  have hH := fullUnitaryCartan_mem Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA p
  let z := W*H p*W*(H p)⁻¹
  have hnH : W ∈ normalizer (Q.tits.B ⊓ Q.tits.N : Set (X ⧸ Q.D)) := by
    rw [←hw]
    exact (normal_subgroupOf_iff_le_normalizer inf_le_right).mp Q.tits.intersection_normal w.val.property
  have hzH : z ∈ Q.tits.B ⊓ Q.tits.N := by
    apply (Q.tits.B ⊓ Q.tits.N).mul_mem _ ((Q.tits.B ⊓ Q.tits.N).inv_mem hH)
    simpa only [hwi] using (mem_normalizer_iff.mp hnH (H p)).mp hH
  have hzR : z ∈ rankOne Q split j := by
    have hwR : W ∈ rankOne Q split j := hw ▸ w.mem_rankOne
    change W*H p*W*(H p)⁻¹ ∈ _
    rw [mul_assoc W (H p) W,mul_assoc]
    exact (rankOne Q split j).mul_mem hwR
      ((mem_normalizer_iff.mp (rankOne_torus_normalizes Q split j hH) W).mp hwR)
  obtain ⟨u,hu⟩ := exists_unitaryTorus_of_mem Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t hzH hzR
  have hwA (a : E) : MulAut.conj W (A a)=(γ (.ofAdd a) : X ⧸ Q.D) := by
    simpa only [MulAut.conj_apply,hwi] using unitaryWeyl_A Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t a
  have hwC (a : E) : MulAut.conj W (γ (.ofAdd a) : X ⧸ Q.D)=A a := by
    simpa only [MulAut.conj_apply,hwi] using unitaryWeyl_C Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t a
  have hHA' (a : E) : MulAut.conj (H p) (A a)=A (((p.1:E)/(p.2:E))*a) := hHA p a
  have hact : z*A ((p.1:E)/(p.2:E))*z⁻¹=A ((p.1:E)*J.conj (p.2:E)) := by
    have he := hHA' 1
    simp only [mul_one] at he
    dsimp only at ⊢
    rw [←he]
    change MulAut.conj z (MulAut.conj (H p) (A 1))=_
    have hzact (x : X ⧸ Q.D) : MulAut.conj z (MulAut.conj (H p) x)=
        MulAut.conj W (MulAut.conj (H p) (MulAut.conj W x)) := by
      simp only [MulAut.conj_apply,z,mul_inv_rev,inv_inv,hwi]
      group
    rw [hzact,hwA]
    change MulAut.conj W (H p*(R).C (.ofAdd 1)*(H p)⁻¹)=_
    rw [hHC]
    change MulAut.conj W (γ (.ofAdd (((p.1:E)*J.conj (p.2:E))*1)) : X ⧸ Q.D)=A ((p.1:E)*J.conj (p.2:E))
    simpa only [mul_one] using hwC ((p.1:E)*J.conj (p.2:E))
  rw [hu,unitaryTorus_A Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA] at hact
  have hscalar : J.conj (u:E)*((p.1:E)/(p.2:E))=(p.1:E)*J.conj (p.2:E) :=
    ξ.injective (Multiplicative.ofAdd.injective
      (alignedSimpleParameter_injective Q split i hVi μ s hact))
  have hu' : u=p.2*Units.map J.conj.toMonoidHom p.2 := by
    apply Units.ext
    apply J.conj.injective
    change J.conj (u:E)=J.conj ((p.2:E)*J.conj (p.2:E))
    rw [map_mul,J.conj_involutive]
    apply mul_right_cancel₀ (div_ne_zero p.1.ne_zero p.2.ne_zero)
    rw [hscalar]
    field_simp
  have he : W*H p*W=U u*H p := by
    rw [←hu]
    dsimp only [z]
    group
  rw [he,hu']
  have hcom : Commute (U (p.2*Units.map J.conj.toMonoidHom p.2))
      (alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)) := by
    let := split.abelian
    exact congrArg Subtype.val (mul_comm
      (⟨_,unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA _⟩ :
        ↥(Q.tits.B ⊓ Q.tits.N))
      (⟨_,alignedTorus_mem_cartan Q split i hVi μ s _⟩ : ↥(Q.tits.B ⊓ Q.tits.N)))
  change U (p.2*Units.map J.conj.toMonoidHom p.2)*
    (alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)*U (unitaryCartanParameter J p)) =
      alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)*
        U (unitaryCartanParameter J (p.1,(Units.map J.conj.toMonoidHom p.2)⁻¹))
  rw [←mul_assoc,hcom.eq,mul_assoc,←map_mul]
  congr 2
  apply Units.ext
  simp only [unitaryCartanParameter,MonoidHom.coe_mk,OneHom.coe_mk,Units.val_mul,
    Units.val_inv_eq_inv_val,Units.coe_map]
  change ((p.2:E)*J.conj (p.2:E))*(J.conj ((p.1:E)*(p.2:E)))⁻¹ =
    (J.conj ((p.1:E)*(J.conj (p.2:E))⁻¹))⁻¹
  rw [map_mul,map_mul,map_inv₀,J.conj_involutive]
  field_simp
variable (hm : rotationOrder Q = 4)
  (hrel : FivePositive.Relations (fiveForm J) (synchronizedRoots Q split i j hVi s μ J b γ ξ))
  (hfirst : ∀ x : E, ∃ p : hermitianUnipotentCoord J, p.val.1=x)
  (hlinD : ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
    let T := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    T*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*T⁻¹ =
      reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) (u:E) p))

include hb hc hk hA hC t hm hrel hfirst hlinD in
/-- The original linear reflection and the marked SU₃ reflection satisfy
the four-term braid, on their actual source values. -/
theorem synchronizedWeyl_braid : ((s.val : X ⧸ Q.D)*W)^4=1 := by
  let w := unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw : (w.val : X ⧸ Q.D)=W :=
    unitaryReflection_val Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw2 : (w.val : X ⧸ Q.D)*(w.val : X ⧸ Q.D)=1 := by
    rw [hw]
    exact unitaryWeyl_square Q split j J hJ θ
  have hwD (p : hermitianUnipotentCoord J) :
      (w.val : X ⧸ Q.D)*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*w.val =
        reflectedUnitaryChart Q split i j s b p := by
    rw [hw]
    exact unitaryWeyl_D Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t hm hrel p
  simpa only [hw] using source_braid_of_unitary_fixed Q split i j hij hVi s μ J b ξ w hm hw2 hwD hfirst hlinD

include hb hc hk hA hC t hHA hHC hm hrel hfirst hlinD in
/-- All remaining Cartan--Weyl presentation clauses for the same synchronized
source roots. The root hypotheses are the already constructed positive laws
and Cartan actions, and no additional Cartan coverage is required. -/
theorem fullUnitaryCartan_weyl_relations :
    (∀ p : Eˣ × Eˣ, (s.val : X ⧸ Q.D)*H p*s.val=H (p.2,p.1)) ∧
    (∀ p : Eˣ × Eˣ, W*H p*W=H (p.1,(Units.map J.conj.toMonoidHom p.2)⁻¹)) ∧
    ((s.val : X ⧸ Q.D)*W)^4=1 :=
  ⟨fullUnitaryCartan_linear_reflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hHA,
    fullUnitaryCartan_unitary_reflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t hHA hHC,
    synchronizedWeyl_braid Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t hm hrel hfirst hlinD⟩
end Source

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
