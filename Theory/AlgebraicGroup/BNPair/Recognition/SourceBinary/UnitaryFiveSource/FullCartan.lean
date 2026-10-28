module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.PositiveRelations


/-!
# The full two-parameter Cartan on the synchronized U₅ source

The natural SU₃ flag forces its diagonal torus into the literal source
Cartan: the unipotent factor in its Borel decomposition would move the
last coordinate axis, so that factor is trivial. The natural A and C
lines give their exact torus weights. Applying this torus to the full
B–A norm identity determines its action on all of D, including its center.

Combining this unitary torus with the already aligned linear coroot gives
a homomorphism from Eˣ × Eˣ into the source Cartan. Its four actions are
exactly FivePresentation.parameters, with both full nonabelian roots.
CartanApplication constructs every premise from the original profile and
generic SU₃ cover, including q=2 and q=4. Weyl and rank-one Bruhat laws
remain separate obligations before the final FiveData construction.
Source: Fong--Seitz II (8C), pp.203–210, especially (8.24)–(8.37).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative Pointwise
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
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
local notation "av" => fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a)
local notation "N" => naturalSectionMap Q split j c
variable (hA : ∀ a : E, (naturalSectionMap Q split j c
  (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])

def unitaryTorus : Eˣ →* X ⧸ Q.D :=
  (rankOne Q split j).subtype.comp (θ.toMonoidHom.comp (hermitianTorusSU J hJ))

include hb in
omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem unitaryTorus_B (u : Eˣ) (p : hermitianUnipotentCoord J) :
    unitaryTorus Q split j J hJ θ u*(b p : X ⧸ Q.D)*(unitaryTorus Q split j J hJ θ u)⁻¹ =
      b (hermitianTorusAction J u p) := by
  have he : hermitianTorusSU J hJ u*hermitianUnipotentSU J hJ p =
      hermitianUnipotentSU J hJ (hermitianTorusAction J u p)*hermitianTorusSU J hJ u :=
    Subtype.ext (hermitianTorusGL_mul_unipotent J u p)
  rw [hb,hb]
  change (θ (hermitianTorusSU J hJ u) : X ⧸ Q.D)*θ (hermitianUnipotentSU J hJ p)*
    (θ (hermitianTorusSU J hJ u) : X ⧸ Q.D)⁻¹ = _
  have hh := congrArg (fun g : J.specialSubgroup => (θ g : X ⧸ Q.D)) he
  simp only [map_mul,coe_mul] at hh
  rw [hh,mul_inv_cancel_right]

include hVj hb in
omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem unitaryTorus_mem_borel (u : Eˣ) : unitaryTorus Q split j J hJ θ u ∈ Q.tits.B := by
  let H := unitaryTorus Q split j J hJ θ
  have hn : H u ∈ normalizer (simpleRoot Q split j : Set (X ⧸ Q.D)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨p,hp⟩ := b.surjective ⟨x,hx⟩
      have hp' : (b p : X ⧸ Q.D) = x := congrArg Subtype.val hp
      rw [←hp',unitaryTorus_B Q split j J hJ θ b hb]
      exact (b _).property
    · intro hx
      obtain ⟨p,hp⟩ := b.surjective ⟨H u*x*(H u)⁻¹,hx⟩
      have he := unitaryTorus_B Q split j J hJ θ b hb u⁻¹ p
      have hp' : (b p : X ⧸ Q.D) = H u*x*(H u)⁻¹ := congrArg Subtype.val hp
      change H u⁻¹*(b p : X ⧸ Q.D)*(H u⁻¹)⁻¹ = _ at he
      rw [map_inv,hp'] at he
      have hx' : x = (b (hermitianTorusAction J u⁻¹ p) : X ⧸ Q.D) := by
        simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he
      rw [hx']
      exact (b _).property
  have hnV := remainder_parabolic_normalizes Q split j hVj
    (rankOne_le_parabolic Q split j (θ (hermitianTorusSU J hJ u)).property)
  have hs : simpleRoot Q split j ⊔ simpleRemainder Q split j = split.U := by
    apply le_antisymm (sup_le (simpleRoot_le Q split j) inf_le_left)
    intro x hx
    have hh : x ∈ (simpleRoot Q split j : Set (X ⧸ Q.D)) * (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]; exact hx
    obtain ⟨a,ha,v,hv,rfl⟩ := hh
    exact mul_mem (mem_sup_left ha) (mem_sup_right hv)
  have he := normalizer_inf_normalizer_le_normalizer_sup
    (simpleRoot Q split j) (simpleRemainder Q split j) ⟨hn,hnV⟩
  rwa [hs,split.normalizer_eq] at he

include hc in
omit [CharP E 2] in
private theorem torus_section_action (a : J.specialSubgroup) (v : simpleRemainder Q split j) :
    (N (remainderRankOneAction Q split j hVj (θ a) v)).toAdd = Matrix.mulVec a.val.val (N v).toAdd := by
  have he := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c (.ofMul (remainderFrattiniAction Q split j hVj (θ a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at he
  rw [remainderFrattiniAction_mk] at he
  exact he

include hA in
omit [CharP E 2] in
private theorem source_A_axis (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ simpleRoot Q split i) :
    ∃ a : E, v = av a ∧ (N v).toAdd = ![0,0,k*J.conj a] := by
  rw [←alignedSimpleParameter_range Q split i hVi μ s] at hv
  obtain ⟨a,ha⟩ := hv
  let z := ξ.symm a.toAdd
  have he : v = av z := by
    apply Subtype.ext
    change (v : X ⧸ Q.D) = alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ z))
    rw [ξ.apply_symm_apply]
    exact ha.symm
  exact ⟨z,he,he.symm ▸ hA z⟩

include hb hc hk hA in
omit [CharP E 2] in
theorem unitaryTorus_mem_cartan (u : Eˣ) :
    unitaryTorus Q split j J hJ θ u ∈ Q.tits.B ⊓ Q.tits.N := by
  let H := unitaryTorus Q split j J hJ θ u
  obtain ⟨a,ha,h,hh,he⟩ := UnitarySource.rootActor_borel_factorization Q split j
    (θ (hermitianTorusSU J hJ u)).property (unitaryTorus_mem_borel Q split j hVj J hJ θ b hb u)
  obtain ⟨p,hp⟩ := b.surjective ⟨a,ha⟩
  have hp' : (b p : X ⧸ Q.D) = a := congrArg Subtype.val hp
  have heH : H = a*h := he
  have hh' : h = (b p : X ⧸ Q.D)⁻¹*H := by rw [hp',heH]; group
  let g := (hermitianUnipotentSU J hJ p)⁻¹*hermitianTorusSU J hJ u
  have hg : (θ g : X ⧸ Q.D) = h := by
    simp only [g,map_mul,map_inv,coe_mul,coe_inv]
    rw [←hb,hh']
    rfl
  let v := remainderRankOneAction Q split j hVj (θ g) (av 1)
  have hv : (v : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    have hn := torus_normalizes_simpleRoot Q split i hh.2
    change (remainderRankOneAction Q split j hVj (θ g) (av 1) : X ⧸ Q.D) ∈ _
    rw [remainderRankOneAction_apply,hg]
    exact (mem_normalizer_iff.mp hn _).mp
      (alignedSimpleParameter_range Q split i hVi μ s ▸ ⟨_,rfl⟩)
  obtain ⟨z,hz,hzv⟩ := source_A_axis Q split i j hij hVi s μ J c ξ k hA v hv
  have hvec := torus_section_action Q split j hVj J θ c hc g (av 1)
  change (N v).toAdd = _ at hvec
  rw [hzv,hA,map_one,mul_one] at hvec
  have h0 := congrFun hvec 0
  have h1 := congrFun hvec 1
  have hm : g.val.val = hermitianUnipotentMatrix J (hermitianUnipotentInv J p)*hermitianTorusMatrix J u := by
    simp only [g,←map_inv]
    rfl
  rw [hm] at h0 h1
  have hp1 : p.val.1 = 0 := by
    have hh : (-J.conj p.val.1)*(u:E)*k = 0 := by
      simpa [hermitianUnipotentMatrix,hermitianUnipotentInv,hermitianTorusMatrix,
        Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_three] using h1.symm
    have hc0 := (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hk)).resolve_right (Units.ne_zero u)
    simpa using hc0
  have hp2 : p.val.2 = 0 := by
    have hh : (-p.val.2)*(u:E)*k = 0 := by
      simpa [hermitianUnipotentMatrix,hermitianUnipotentInv,hermitianTorusMatrix,
        Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_three,hp1] using h0.symm
    have hc0 := (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hk)).resolve_right (Units.ne_zero u)
    simpa using hc0
  have hpone : p = 1 := Subtype.ext (Prod.ext hp1 hp2)
  rw [hpone,map_one] at hp'
  rw [←hp',coe_one,one_mul] at he
  change (θ (hermitianTorusSU J hJ u) : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N
  rw [he]
  exact hh.2


include hb hc hk hA in
omit [CharP E 2] in
theorem unitaryTorus_A (u : Eˣ) (a : E) :
    unitaryTorus Q split j J hJ θ u*A a*(unitaryTorus Q split j J hJ θ u)⁻¹ =
      A (J.conj (u:E)*a) := by
  let g := hermitianTorusSU J hJ u
  let v := remainderRankOneAction Q split j hVj (θ g) (av a)
  have hH := unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA u
  have hv : (v : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    rw [remainderRankOneAction_apply]
    exact (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split i hH) _).mp
      (alignedSimpleParameter_range Q split i hVi μ s ▸ ⟨_,rfl⟩)
  obtain ⟨z,hz,hzv⟩ := source_A_axis Q split i j hij hVi s μ J c ξ k hA v hv
  have hvec := torus_section_action Q split j hVj J θ c hc g (av a)
  change (N v).toAdd = _ at hvec
  rw [hzv,hA] at hvec
  change ![0,0,k*J.conj z] = Matrix.mulVec (hermitianTorusMatrix J u) ![0,0,k*J.conj a] at hvec
  have he : k*J.conj z = (u:E)*(k*J.conj a) := by
    simpa [g,hermitianTorusMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
      using congrFun hvec 2
  have hz' : z = J.conj (u:E)*a := by
    apply J.conj.injective
    rw [map_mul,J.conj_involutive]
    apply mul_left_cancel₀ hk
    calc
      _ = (u:E)*(k*J.conj a) := he
      _ = _ := by ring
  have hvval := congrArg Subtype.val hz
  rw [remainderRankOneAction_apply,hz'] at hvval
  exact hvval

variable (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (hC : ∀ a : E, (naturalSectionMap Q split j c (inclusion (opposite_roots_le_remainder Q split i j hij).2
    (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0])

include hb hc hk hA hC in
omit [CharP E 2] in
theorem unitaryTorus_C (u : Eˣ) (a : E) :
    unitaryTorus Q split j J hJ θ u*(γ (.ofAdd a) : X ⧸ Q.D)*(unitaryTorus Q split j J hJ θ u)⁻¹ =
      γ (.ofAdd ((u:E)⁻¹*a)) := by
  let g := hermitianTorusSU J hJ u
  let cv := inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a))
  let v := remainderRankOneAction Q split j hVj (θ g) cv
  have hH := unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA u
  have hv : (v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    rw [remainderRankOneAction_apply]
    exact (mem_normalizer_iff.mp (rootAt_torus_normalizes Q split i (Q.simple j) hH) _).mp
      (γ (.ofAdd a)).property
  obtain ⟨z,hz⟩ := γ.surjective ⟨v,hv⟩
  have hzv : v = inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ z) :=
    Subtype.ext (congrArg Subtype.val hz).symm
  have hvec := torus_section_action Q split j hVj J θ c hc g cv
  change (N v).toAdd = _ at hvec
  rw [hzv] at hvec
  change (N (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd z.toAdd)))).toAdd = _ at hvec
  rw [hC,hC] at hvec
  change ![k*J.conj z.toAdd,0,0] = Matrix.mulVec (hermitianTorusMatrix J u) ![k*J.conj a,0,0] at hvec
  have he : k*J.conj z.toAdd = (J.conj (u:E))⁻¹*(k*J.conj a) := by
    simpa [g,hermitianTorusMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
      using congrFun hvec 0
  have hz' : z.toAdd = (u:E)⁻¹*a := by
    apply J.conj.injective
    rw [map_mul,map_inv₀]
    apply mul_left_cancel₀ hk
    calc
      _ = (J.conj (u:E))⁻¹*(k*J.conj a) := he
      _ = _ := by ring
  have hvval := congrArg Subtype.val hzv
  rw [remainderRankOneAction_apply] at hvval
  change unitaryTorus Q split j J hJ θ u*(γ (.ofAdd a) : X ⧸ Q.D)*
    (unitaryTorus Q split j J hJ θ u)⁻¹ = γ (.ofAdd z.toAdd) at hvval
  rwa [hz'] at hvval

section CrossAction
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
variable {Y : Type*} [Group Y]
  (r : PositiveMaps Y (Multiplicative E) (FivePositive.Parameter (fiveForm J))
    (Multiplicative E) (FivePositive.Parameter (fiveForm J)))
  (hBA : ∀ (p : hermitianUnipotentCoord J) a,
    r.B p*r.A (.ofAdd a) = r.A (.ofAdd a)*r.D (FivePositive.normParameter (fiveForm J) a p)*
      r.C (.ofAdd (a*J.conj p.val.2))*r.B p)

include hBA in
omit [CharP E 2] [Algebra (ZMod 2) E] in
/-- The full mixed norm identity determines the unitary torus action on D,
including its center, from its known actions on A, B and C. -/
theorem unitary_cross_action (u : Eˣ) (α : Y ≃* Y)
    (hB : ∀ p : hermitianUnipotentCoord J, α (r.B p) = r.B (hermitianTorusAction J u p))
    (hA : ∀ a, α (r.A (.ofAdd a)) = r.A (.ofAdd (J.conj (u:E)*a)))
    (hC : ∀ a, α (r.C (.ofAdd a)) = r.C (.ofAdd ((u:E)⁻¹*a)))
    (p : hermitianUnipotentCoord J) :
    α (r.D p) = r.D (FivePositive.normParameter (fiveForm J) (J.conj (u:E))
      (hermitianTorusAction J u p)) := by
  have hn : FivePositive.normParameter (fiveForm J) 1 p = p := by
    apply Subtype.ext
    simp [FivePositive.normParameter]
  have he := congrArg α (hBA p 1)
  simp only [map_mul,hB,hA,hC,hn,one_mul,mul_one] at he
  have ht := hBA (hermitianTorusAction J u p) (J.conj (u:E))
  have hc : J.conj (u:E)*J.conj (hermitianTorusAction J u p).val.2 =
      (u:E)⁻¹*J.conj p.val.2 := by
    change J.conj (u:E)*J.conj (p.val.2*(J.conj (u:E))⁻¹*(u:E)⁻¹) = _
    simp only [map_mul,map_inv₀]
    rw [J.conj_involutive]
    field_simp
  rw [hc] at ht
  have hh := he.symm.trans ht
  exact mul_left_cancel (mul_right_cancel (mul_right_cancel hh))
end CrossAction


open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation

/-- The second rank-one torus parameter for the prescribed diagonal pair. -/
def unitaryCartanParameter : (Eˣ × Eˣ) →* Eˣ where
  toFun p := (Units.map J.conj.toMonoidHom (p.1*p.2))⁻¹
  map_one' := by simp
  map_mul' p q := by simp; ac_rfl

include hb hc hk hA in
/-- The full two-parameter Cartan, assembled inside the literal source H. -/
def fullUnitaryCartan : (Eˣ × Eˣ) →* X ⧸ Q.D where
  toFun p := alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)*
    unitaryTorus Q split j J hJ θ (unitaryCartanParameter J p)
  map_one' := by simp only [map_one, Prod.fst_one, mul_one]
  map_mul' p q := by
    simp only [Prod.fst_mul,map_mul]
    have he : Commute
        (alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom q.1))
        (unitaryTorus Q split j J hJ θ (unitaryCartanParameter J p)) := by
      let := split.abelian
      exact congrArg Subtype.val (mul_comm
        (⟨_,alignedTorus_mem_cartan Q split i hVi μ s _⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
        (⟨_,unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA _⟩ :
          ↥(Q.tits.B ⊓ Q.tits.N)))
    exact he.mul_mul_mul_comm _ _

include hb hc hk hA in
omit [CharP E 2] in
theorem fullUnitaryCartan_mem (p : Eˣ × Eˣ) :
    fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA p ∈ Q.tits.B ⊓ Q.tits.N :=
  (Q.tits.B ⊓ Q.tits.N).mul_mem (alignedTorus_mem_cartan Q split i hVi μ s _)
    (unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA _)

section Parameters
omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem fullCartan_A_scalar (p : Eˣ × Eˣ) (a : E) :
    (p.1:E)^2*(J.conj (unitaryCartanParameter J p : E)*a) = ((p.1:E)/(p.2:E))*a := by
  simp only [unitaryCartanParameter,MonoidHom.coe_mk,OneHom.coe_mk,Units.val_inv_eq_inv_val,Units.coe_map,Units.val_mul]
  change (p.1:E)^2*(J.conj ((J.conj ((p.1:E)*(p.2:E)))⁻¹)*a) = _
  rw [map_inv₀, J.conj_involutive]
  field_simp

omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem fullCartan_C_scalar (p : Eˣ × Eˣ) (a : E) :
    ((p.1:E)/J.conj (p.1:E))*((unitaryCartanParameter J p : E)⁻¹*a) =
      ((p.1:E)*J.conj (p.2:E))*a := by
  simp only [unitaryCartanParameter,MonoidHom.coe_mk,OneHom.coe_mk,Units.val_inv_eq_inv_val,Units.coe_map,Units.val_mul]
  change ((p.1:E)/J.conj (p.1:E))*(((J.conj ((p.1:E)*(p.2:E)))⁻¹)⁻¹*a) = _
  rw [inv_inv, map_mul]
  field_simp

omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem fullCartan_B_parameter (p : Eˣ × Eˣ) (v : hermitianUnipotentCoord J) :
    FivePositive.normParameter (fiveForm J) (↑p.1⁻¹:E)
      (hermitianTorusAction J (unitaryCartanParameter J p) v) =
        FiveTorus.scale (fiveForm J) p p.2 v := by
  have hcc (a : E) : J.conj (J.conj a) = a := J.conj_involutive a
  apply Subtype.ext
  apply Prod.ext <;>
    simp [FivePositive.normParameter,FiveTorus.scale,hermitianTorusAction,unitaryCartanParameter,
      Matrix5.delta,fiveForm,Theory.SpecificGroups.UnitaryFive.identityForm,map_mul,map_inv₀,hcc] <;> field_simp

omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem fullCartan_D_parameter (p : Eˣ × Eˣ) (v : hermitianUnipotentCoord J) :
    FivePositive.normParameter (fiveForm J) (p.1:E)
      (FivePositive.normParameter (fiveForm J) (J.conj (unitaryCartanParameter J p : E))
        (hermitianTorusAction J (unitaryCartanParameter J p) v)) =
          FiveTorus.scale (fiveForm J) p p.1 v := by
  have hcc (a : E) : J.conj (J.conj a) = a := J.conj_involutive a
  apply Subtype.ext
  apply Prod.ext <;>
    simp [FivePositive.normParameter,FiveTorus.scale,hermitianTorusAction,unitaryCartanParameter,
      Matrix5.delta,fiveForm,Theory.SpecificGroups.UnitaryFive.identityForm,map_mul,map_inv₀,hcc] <;> field_simp
end Parameters

variable (hrel : FivePositive.Relations (fiveForm J)
    (synchronizedRoots Q split i j hVi s μ J b γ ξ))
  (hlinA : ∀ (u : Eˣ) a,
    let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    H*alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ a))*H⁻¹ =
      alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ ((u:E)^2*a))))
  (hlinC : ∀ (u : Eˣ) a,
    let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    H*(γ (.ofAdd a) : X ⧸ Q.D)*H⁻¹ = γ (.ofAdd (((u:E)/J.conj (u:E))*a)))
  (hlinBD : ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
    let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    H*(b p : X ⧸ Q.D)*H⁻¹ = b (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p) ∧
    H*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*H⁻¹ =
      reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) (u:E) p))

include hb hc hk hA hC hrel hlinA hlinC hlinBD in
/-- All four full-Cartan equations in the literal U₅ presentation parameters. -/
theorem synchronizedRoots_full_cartan :
    let r := synchronizedRoots Q split i j hVi s μ J b γ ξ
    let H := fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA
    (∀ p a, H p*r.A (.ofAdd a)*(H p)⁻¹ = r.A (.ofAdd (((p.1:E)/(p.2:E))*a))) ∧
    (∀ p a, H p*r.C (.ofAdd a)*(H p)⁻¹ = r.C (.ofAdd (((p.1:E)*J.conj (p.2:E))*a))) ∧
    (∀ p v, H p*r.B v*(H p)⁻¹ = r.B (FiveTorus.scale (fiveForm J) p p.2 v)) ∧
    ∀ p v, H p*r.D v*(H p)⁻¹ = r.D (FiveTorus.scale (fiveForm J) p p.1 v) := by
  let r := synchronizedRoots Q split i j hVi s μ J b γ ξ
  let U := unitaryTorus Q split j J hJ θ
  let H := fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA
  have hUa (u : Eˣ) a : U u*r.A (.ofAdd a)*(U u)⁻¹ = r.A (.ofAdd (J.conj (u:E)*a)) :=
    unitaryTorus_A Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA u a
  have hUc (u : Eˣ) a : U u*r.C (.ofAdd a)*(U u)⁻¹ = r.C (.ofAdd ((u:E)⁻¹*a)) :=
    unitaryTorus_C Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC u a
  have hUb (u : Eˣ) v : U u*r.B v*(U u)⁻¹ = r.B (hermitianTorusAction J u v) :=
    unitaryTorus_B Q split j J hJ θ b hb u v
  have hUd (u : Eˣ) v : U u*r.D v*(U u)⁻¹ = r.D
      (FivePositive.normParameter (fiveForm J) (J.conj (u:E)) (hermitianTorusAction J u v)) :=
    unitary_cross_action J r (fun p a => hrel.BA a p) u (MulAut.conj (U u)) (hUb u) (hUa u) (hUc u) v
  have hprod (p : Eˣ × Eˣ) (x : X ⧸ Q.D) :
      H p*x*(H p)⁻¹ = alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)*
        (U (unitaryCartanParameter J p)*x*(U (unitaryCartanParameter J p))⁻¹)*
          (alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom p.1))⁻¹ := by
    change (alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)*U (unitaryCartanParameter J p))*x*
      (alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom p.1)*U (unitaryCartanParameter J p))⁻¹ = _
    group
  refine ⟨?_,?_,?_,?_⟩
  · intro p a
    change H p*r.A (.ofAdd a)*(H p)⁻¹ = _
    rw [hprod,hUa]
    change _*A _*_ = _
    rw [hlinA]
    change A ((p.1:E)^2*(J.conj (unitaryCartanParameter J p : E)*a)) = A (((p.1:E)/(p.2:E))*a)
    rw [fullCartan_A_scalar]
  · intro p a
    change H p*r.C (.ofAdd a)*(H p)⁻¹ = _
    rw [hprod,hUc]
    change _*(γ _ : X ⧸ Q.D)*_ = _
    rw [hlinC,fullCartan_C_scalar]
    rfl
  · intro p v
    change hermitianUnipotentCoord J at v
    change H p*r.B v*(H p)⁻¹ = _
    erw [hprod,hUb]
    change _*(b _ : X ⧸ Q.D)*_ = _
    erw [(hlinBD p.1 _).1,fullCartan_B_parameter J p v]
    rfl
  · intro p v
    change hermitianUnipotentCoord J at v
    change H p*r.D v*(H p)⁻¹ = _
    erw [hprod,hUd]
    change _*(reflectedUnitaryChart Q split i j s b _ : X ⧸ Q.D)*_ = _
    erw [(hlinBD p.1 (FivePositive.normParameter (fiveForm J) (J.conj (unitaryCartanParameter J p : E))
      (hermitianTorusAction J (unitaryCartanParameter J p) v))).2,fullCartan_D_parameter J p v]
    rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
