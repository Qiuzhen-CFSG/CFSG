module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.OuterSylow
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.FieldTheory.QuadraticFrobeniusTrace
/-!
# Field-involution descent inside the marked symplectic Borel

Four unipotent coordinates and additive quadratic trace solve every
field-involution cocycle inside the original unipotent subgroup. Scalar
multiplicative cocycles first remove the two diagonal characters, giving
descent inside the whole Borel. Hence an outer involution preserving the
standard flag is conjugate to an actual field involution by that same Borel.

This keeps the original unipotent group and its root centers in place.
The two fixed simple-root elements at parameter one show that the
centralizer of the fixed unipotent subgroup, inside the original unipotent
group, is central. The calculation includes the binary fixed field; it does
not assert the nontrivial root intersection which fails in that exception.

Source: Aschbacher--Smith F.4.29(2),(7) and F.4.37, printed pp.289,293
of refs/quasithin.pdf. The Chapter 6 consumer uses the same original outer
involution and whole-middle comparison, without any recognized completion.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem field_element (σ : F ≃+* F) (b u w v : F) :
    fieldAutomorphism σ (element b u w v).val =
      (element (σ b) (σ u) (σ w) (σ v)).val := by
  apply Subtype.ext
  change (element b u w v).val.val.map σ = _
  rw [element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks]

omit [Finite F] in
private theorem trace_solution (σ : F ≃+* F) (hσ : σ^2=1) (hne : σ≠1)
    (x : F) (hx : σ x=x) : ∃ y, y+σ y=x := by
  apply InvolutiveTrace.exists_trace σ _ _ x hx
  · intro t
    exact congrArg (fun s : F ≃+* F => s t) hσ
  · by_contra! hh
    exact hne (RingEquiv.ext hh)

/-- Every field-involution cocycle in the actual unipotent subgroup is a
coboundary in that same subgroup, including the binary fixed field. -/
theorem unipotent_field_coboundary (σ : F ≃+* F) (hσ : σ^2=1) (hne : σ≠1)
    (g : unipotent (F := F)) (hg : g.val * fieldAutomorphism σ g.val = 1) :
    ∃ c : unipotent (F := F), g.val = c.val * (fieldAutomorphism σ c.val)⁻¹ := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  rw [field_element] at hg
  have hh : element b u w v * element (σ b) (σ u) (σ w) (σ v) = 1 := Subtype.ext hg
  rw [element_mul,←element_zero,element_eq_iff] at hh
  have hb : σ b=b := (CharTwo.add_eq_zero.mp hh.1).symm
  have hv : σ v=v := (CharTwo.add_eq_zero.mp hh.2.2.2).symm
  obtain ⟨c,hc⟩ := trace_solution σ hσ hne b hb
  obtain ⟨a,ha⟩ := trace_solution σ hσ hne v hv
  have hw : σ (w+v*σ c)=w+v*σ c := by
    have hcc : σ (σ c)=c := congrArg (fun s : F ≃+* F => s c) hσ
    simp only [map_add,map_mul,hv,hcc]
    have h := hh.2.2.1
    rw [hb] at h
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h + v*hc
  obtain ⟨t,ht⟩ := trace_solution σ hσ hne (w+v*σ c) hw
  have hu : σ (u+b*σ t+w*σ c+b*v*σ c)=u+b*σ t+w*σ c+b*v*σ c := by
    have hcc : σ (σ c)=c := congrArg (fun s : F ≃+* F => s c) hσ
    have htt : σ (σ t)=t := congrArg (fun s : F ≃+* F => s t) hσ
    simp only [map_add,map_mul,hb,hv,hcc,htt]
    have h := hh.2.1
    rw [hb] at h
    have hW := hh.2.2.1
    rw [hb] at hW
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h + b*ht + (c+b)*hW + w*hc
  obtain ⟨z,hz⟩ := trace_solution σ hσ hne _ hu
  refine ⟨element c z t a, (eq_mul_inv_iff_mul_eq).mpr ?_⟩
  rw [field_element]
  change (element b u w v * element (σ c) (σ z) (σ t) (σ a)).val = _
  apply congrArg (fun x : unipotent (F := F) => x.val)
  rw [element_mul,element_eq_iff]
  constructor
  · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc
  constructor
  · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hz
  constructor
  · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) ht
  · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) ha

private def fieldBorel (σ : F ≃+* F) : borel (F := F) →* borel (F := F) :=
  ((fieldAutomorphism σ).toMonoidHom.comp (borel (F := F)).subtype).codRestrict _ (by
    intro g
    constructor
    · rw [←field_map_pointParabolic σ]
      exact mem_map_of_mem _ g.property.1
    · rw [←field_map_planeParabolic σ]
      exact mem_map_of_mem _ g.property.2)

omit [Finite F] in
private theorem unit_coboundary (σ : F ≃+* F) (a : Fˣ)
    (ha : a * Units.map σ.toMonoidHom a = 1) :
    ∃ c : Fˣ, a = c * (Units.map σ.toMonoidHom c)⁻¹ := by
  by_cases he : a=1
  · subst a
    exact ⟨1, by simp⟩
  have hnorm : (a:F)*σ (a:F)=1 := congrArg Units.val ha
  have hp : (a:F) ≠ -1 := by
    intro hh
    apply he
    exact Units.ext (by simpa only [CharTwo.neg_eq,Units.val_one] using hh)
  let c : Fˣ := Units.mk0 (1+(a:F)) (by
    intro hh
    exact hp (eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hh)))
  refine ⟨c, Units.ext ?_⟩
  simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.coe_map]
  change (a:F) = (1+(a:F)) * (σ (1+(a:F)))⁻¹
  rw [←div_eq_mul_inv]
  apply (eq_div_iff ((map_ne_zero σ).mpr c.ne_zero)).mpr
  change (a:F) * σ (1+(a:F)) = 1+(a:F)
  rw [map_add,map_one,mul_add,hnorm,mul_one,add_comm]

omit [Finite F] [CharP F 2] in
private theorem characters_field (σ : F ≃+* F) (g : borel (F := F)) :
    borelCharacters (fieldBorel σ g) =
      (Units.map σ.toMonoidHom (borelCharacters g).1,
       Units.map σ.toMonoidHom (borelCharacters g).2) := by
  apply Prod.ext <;> apply Units.ext
  · change (determinantCharacter (point F) _) = σ (determinantCharacter (point F) _ : F)
    rw [point_determinant,point_determinant]
    rfl
  · change (determinantCharacter (plane F) _) = σ (determinantCharacter (plane F) _ : F)
    rw [plane_determinant,plane_determinant]
    change σ _ * σ _ - σ _ * σ _ = _
    simp only [map_sub,map_mul]
    rfl

/-- Field cocycles in the full Borel can be killed inside that Borel. -/
theorem borel_field_coboundary (σ : F ≃+* F) (hσ : σ^2=1) (hne : σ≠1)
    (g : borel (F := F)) (hg : g.val * fieldAutomorphism σ g.val = 1) :
    ∃ c : borel (F := F), g.val = c.val * (fieldAutomorphism σ c.val)⁻¹ := by
  have hgB : g * fieldBorel σ g=1 := Subtype.ext hg
  have hc := congrArg borelCharacters hgB
  rw [map_mul,map_one,characters_field] at hc
  obtain ⟨a,ha⟩ := unit_coboundary σ (borelCharacters g).1 (congrArg Prod.fst hc)
  obtain ⟨b,hb⟩ := unit_coboundary σ (borelCharacters g).2 (congrArg Prod.snd hc)
  let c := EvenBorelTorus.torusSection (a,b)
  let v := c⁻¹*g*fieldBorel σ c
  have hvU : v.val ∈ unipotent := by
    apply (borelCharacters_eq_one v).mp
    change borelCharacters (c⁻¹*g*fieldBorel σ c)=1
    rw [map_mul,map_mul,map_inv,characters_field]
    have hcc : borelCharacters c=(a,b) := EvenBorelTorus.characters_torusSection _
    rw [hcc]
    apply Prod.ext
    · change a⁻¹*(borelCharacters g).1*Units.map σ.toMonoidHom a=1
      rw [ha]; group
    · change b⁻¹*(borelCharacters g).2*Units.map σ.toMonoidHom b=1
      rw [hb]; group
  have hact (x : Sp F) : fieldAutomorphism σ (fieldAutomorphism σ x)=x := by
    have hs : (fieldAutomorphism σ)^2=1 := by
      change fieldAutomorphismHom σ^2=1
      rw [←map_pow,hσ,map_one]
    exact congrArg (fun a : MulAut (Sp F) => a x) hs
  have hv : v.val * fieldAutomorphism σ v.val=1 := by
    change (c.val⁻¹*g.val*fieldAutomorphism σ c.val) *
      fieldAutomorphism σ (c.val⁻¹*g.val*fieldAutomorphism σ c.val)=1
    simp only [map_mul,map_inv,hact]
    calc
      _ = c.val⁻¹*(g.val*fieldAutomorphism σ g.val)*c.val := by group
      _ = 1 := by rw [hg]; group
  obtain ⟨u,hu⟩ := unipotent_field_coboundary σ hσ hne ⟨v.val,hvU⟩ hv
  refine ⟨c * inclusion unipotent_le_borel u,?_⟩
  change g.val = (c.val*u.val) * (fieldAutomorphism σ (c.val*u.val))⁻¹
  change c.val⁻¹*g.val*fieldAutomorphism σ c.val =
    u.val*(fieldAutomorphism σ u.val)⁻¹ at hu
  rw [map_mul]
  calc
    g.val = c.val*(c.val⁻¹*g.val*fieldAutomorphism σ c.val)*
      (fieldAutomorphism σ c.val)⁻¹ := by group
    _ = _ := by rw [hu]; group

/-- An outer involution preserving the marked flag is conjugate to a field
involution by an element of the same full Borel. -/
theorem outer_flag_involution_normal_form {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    ∃ σ : F ≃+* F, orderOf σ=2 ∧ ∃ c : borel (F := F),
      a = MulAut.conj c.val * fieldAutomorphism σ * (MulAut.conj c.val)⁻¹ := by
  obtain ⟨g,σ,he⟩ := SemilinearClassification.inner_field_of_preservesDiagram a
    (SourceNormalizerExtension.flag_preservesDiagram ⟨a,ha⟩)
  have hgflag : MulAut.conj g ∈ SourceNormalizerExtension.flagAutomorphisms F := by
    have hfield : fieldAutomorphism σ ∈ SourceNormalizerExtension.flagAutomorphisms F :=
      ⟨field_map_pointParabolic σ,field_map_planeParabolic σ⟩
    have hh := (SourceNormalizerExtension.flagAutomorphisms F).mul_mem ha
      ((SourceNormalizerExtension.flagAutomorphisms F).inv_mem hfield)
    rwa [he,mul_inv_cancel_right] at hh
  have hgB : g ∈ borel := (SourceNormalizerExtension.inner_flag_iff hF hn g).mp hgflag
  have hσne : σ≠1 := by
    intro hh
    apply hi
    rw [he,hh]
    change MulAut.conj g * fieldAutomorphismHom 1 ∈ _
    rw [map_one,mul_one]
    exact ⟨g,rfl⟩
  let π : MulAut (Sp F) →* MulAut.Outer (Sp F) := QuotientGroup.mk' _
  have hπ : π a=outerFieldHom σ := by
    rw [he,map_mul]
    have hg : π (MulAut.conj g)=1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [hg,one_mul]
    rfl
  have ha2 : a^2=1 := by simpa only [hao] using pow_orderOf_eq_one a
  have hσ2 : σ^2=1 := by
    apply outerFieldHom_injective
    rw [map_pow,←hπ,←map_pow,ha2,map_one,map_one]
  have hfield2 : (fieldAutomorphism σ)^2=1 := by
    change fieldAutomorphismHom σ^2=1
    rw [←map_pow,hσ2,map_one]
  have hg : g * fieldAutomorphism σ g=1 :=
    (inner_twist_square_eq_one_iff _ hfield2 g).mp (he ▸ ha2)
  obtain ⟨c,hc⟩ := borel_field_coboundary σ hσ2 hσne ⟨g,hgB⟩ hg
  exact ⟨σ,orderOf_eq_prime hσ2 hσne,c,he.trans (inner_twist_eq_conjugate _ g c.val hc)⟩

/-- Inside the original unipotent group, the centralizer of the fixed
unipotent group is exactly its central two-root plane. The Borel conjugator
keeps this assertion in the original coordinates. -/
theorem unipotent_centralizer_fixed_le_center {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    unipotent ⊓ centralizer ((unipotent ⊓ a.fixedSubgroup : Subgroup (Sp F)) : Set (Sp F)) ≤
      (center (unipotent (F := F))).map unipotent.subtype := by
  obtain ⟨σ,_,c,hc⟩ := outer_flag_involution_normal_form hF hn a hao ha hi
  have hcN : c.val ∈ normalizer (unipotent (F := F) : Set (Sp F)) := by
    rw [←borel_eq_normalizer_unipotent]
    exact c.property
  let e : MulAut (unipotent (F := F)) := unipotent.normalizerMonoidHom ⟨c.val,hcN⟩
  have he (x : unipotent (F := F)) : (e x).val=c.val*x.val*c.val⁻¹ := rfl
  have hfixed (y : unipotent (F := F)) (hy : fieldAutomorphism σ y.val=y.val) :
      (e y).val ∈ unipotent ⊓ a.fixedSubgroup := by
    refine ⟨(e y).property,?_⟩
    apply (MulAut.mem_fixedSubgroup a (e y).val).mpr
    rw [hc,he]
    rw [show (MulAut.conj c.val)⁻¹ = MulAut.conj (c.val⁻¹) from
      (map_inv MulAut.conj c.val).symm]
    simp only [MulAut.mul_apply,MulAut.conj_apply,inv_inv]
    simp only [mul_assoc,inv_mul_cancel,mul_one,inv_mul_cancel_left,hy]
  rintro x ⟨hxU,hxC⟩
  let xU : unipotent (F := F) := ⟨x,hxU⟩
  have hcomm (y : unipotent (F := F)) (hy : fieldAutomorphism σ y.val=y.val) :
      y*e.symm xU=e.symm xU*y := by
    apply e.injective
    rw [map_mul,map_mul,e.apply_symm_apply]
    exact Subtype.ext (hxC _ (hfixed y hy))
  have hxZ : e.symm xU ∈ center (unipotent (F := F)) := by
    obtain ⟨⟨b,u,w,v⟩,hex⟩ := element_surjective (e.symm xU)
    rw [←hex,mem_center_iff_coordinates]
    have h1 := hcomm (element 0 0 0 1) (by rw [field_element]; simp only [map_zero,map_one])
    have h2 := hcomm (element 1 0 0 0) (by rw [field_element]; simp only [map_zero,map_one])
    rw [←hex,element_mul,element_mul,element_eq_iff] at h1 h2
    exact ⟨by simpa using h1.2.2.1, by simpa using h2.2.2.1.symm⟩
  have hxZ' : xU ∈ center (unipotent (F := F)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul,e.apply_symm_apply] using congrArg e ((mem_center_iff.mp hxZ) z)
  exact mem_map_of_mem unipotent.subtype hxZ'
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
