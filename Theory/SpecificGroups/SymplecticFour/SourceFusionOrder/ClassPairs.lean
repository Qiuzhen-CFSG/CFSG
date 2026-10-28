module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.CentralFusion

/-!
# Pinned involutions and compatible parabolic class paths

The three nonempty coordinate support patterns in the native Sylow center
have representatives theta(1,0), theta(0,1), theta(1,1). The diagonal Cartan
is transitive on each pattern. Together with the parabolic conjugators into
the center, this gives a conjugator in one actual parabolic from every
Sylow involution to a pinned representative. Compatible maps from both
parabolics transport the same class path. No isomorphism of a completion
is required and irredundance of the three classes is not asserted here.

Source: the symplectic case of Aschbacher--Smith F.4.27,30,35, printed
pp.288--292 of refs/quasithin.pdf, used for the F.4.43 class comparison.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

@[expose] def centralRepresentative (i : Fin 3) : unipotent (F := F) :=
  ![theta 1 0,theta 0 1,theta 1 1] i

@[expose] def borelRepresentative (i : Fin 3) : borel (F := F) :=
  inclusion unipotent_le_borel (centralRepresentative i)

theorem centralRepresentative_center (i : Fin 3) :
    centralRepresentative (F := F) i∈center (unipotent (F := F)) := by
  fin_cases i <;> exact theta_mem_center _ _

omit [Finite F] in
theorem centralRepresentative_order (i : Fin 3) :
    orderOf (centralRepresentative (F := F) i)=2 := by
  apply orderOf_eq_prime
  · fin_cases i <;> simp [centralRepresentative,theta,element_square,element_zero]
  · intro he
    fin_cases i <;>
      simp [centralRepresentative,theta,←element_zero,element_eq_iff] at he

private theorem diagonal_orbit (s t u v : F)
    (hs : s = 0 ↔ u = 0) (ht : t = 0 ↔ v = 0) :
    ∃ b ∈ borel (F := F), b * (theta s t).val * b⁻¹ = (theta u v).val := by
  have scalar (x y : F) (hxy : x = 0 ↔ y = 0) :
      ∃ c : Fˣ, (c : F) * x = y := by
    by_cases hx : x = 0
    · exact ⟨1,by simp [hx,hxy.mp hx]⟩
    exact ⟨Units.mk0 (y/x) (div_ne_zero (mt hxy.mpr hx) hx), by simp [hx]⟩
  obtain ⟨c,hc⟩ := scalar s u hs
  obtain ⟨d,hd⟩ := scalar t v ht
  obtain ⟨a,ha⟩ := RootTori.weight_surjective (F := F) 0 c
  have ha' : a^2 = c := by simpa [RootTori.weight] using ha
  refine ⟨diagonalTorusHom (a,a⁻¹*d),diagonalTorus_mem_borel _ _,?_⟩
  have hh := diagonalTorus_weights (a,a⁻¹*d) s t
  rw [show (a:F)^2*s=u by rw [←Units.val_pow_eq_pow_val,ha']; exact hc,
    show (a:F)*((a⁻¹*d : Fˣ):F)*t=v by simpa using hd] at hh
  simpa only [parameter_apply, theta_val, toAdd_ofAdd] using hh


/-- Each nonidentity center element has a Borel conjugator to one of the
three pinned support patterns. -/
theorem center_conjugate_representative (x : unipotent (F := F))
    (hx : x∈center (unipotent (F := F))) (hne : x≠1) :
    ∃ i : Fin 3, ∃ b∈borel (F := F), b*x.val*b⁻¹=(centralRepresentative i).val := by
  obtain ⟨⟨s,t⟩,he⟩ := (theta_range (F := F)).ge hx
  change theta s.toAdd t.toAdd=x at he
  subst x
  by_cases hs : s.toAdd=0
  · have ht : t.toAdd≠0 := by
      intro ht
      apply hne
      simp [hs,ht,theta,element_zero]
    obtain ⟨b,hb,he⟩ := diagonal_orbit s.toAdd t.toAdd 0 1 (by simp [hs]) (by simp [ht])
    exact ⟨1,b,hb,he⟩
  by_cases ht : t.toAdd=0
  · obtain ⟨b,hb,he⟩ := diagonal_orbit s.toAdd t.toAdd 1 0 (by simp [hs]) (by simp [ht])
    exact ⟨0,b,hb,he⟩
  obtain ⟨b,hb,he⟩ := diagonal_orbit s.toAdd t.toAdd 1 1 (by simp [hs]) (by simp [ht])
  exact ⟨2,b,hb,he⟩

/-- The three class paths use a conjugator in one actual endpoint. -/
theorem involution_parabolic_conjugate_representative
    (x : unipotent (F := F)) (hx : orderOf x=2) :
    ∃ i : Fin 3, ∃ g : Sp F, (g∈pointParabolic ∨ g∈planeParabolic) ∧
      g*x.val*g⁻¹=(centralRepresentative i).val := by
  obtain ⟨g,hg,z,hz,he⟩ := involution_parabolic_conjugate_center x
    ((orderOf_eq_prime_iff.mp hx).1)
  have hzne : z≠1 := by
    intro hh
    have hh' : (MulAut.conj g) x.val=1 := he.trans (congrArg Subtype.val hh)
    have hx1 : x=1 := Subtype.ext ((MulAut.conj g).map_eq_one_iff.mp hh')
    simp [hx1] at hx
  obtain ⟨i,b,hb,hbz⟩ := center_conjugate_representative z hz hzne
  refine ⟨i,b*g,?_,?_⟩
  · exact hg.elim
      (fun hg => Or.inl (pointParabolic.mul_mem hb.1 hg))
      (fun hg => Or.inr (planeParabolic.mul_mem hb.2 hg))
  · calc
      (b*g)*x.val*(b*g)⁻¹ = b*(g*x.val*g⁻¹)*b⁻¹ := by group
      _ = _ := by rw [he,hbz]

/-- Compatible maps on the two parabolics preserve the same three class
paths. The source and native conjugators use the same endpoint witness. -/
theorem compatible_class_pair {J : Type*} [Group J]
    (f : pointParabolic (F := F)→*J) (g : planeParabolic (F := F)→*J)
    (hag : ∀ b : borel (F := F), f (inclusion inf_le_left b)=g (inclusion inf_le_right b))
    (x : unipotent (F := F)) (hx : orderOf x=2) :
    ∃ i : Fin 3,
      IsConj (f (inclusion inf_le_left (borelRepresentative i)))
        (f (inclusion (unipotent_le_borel.trans inf_le_left) x)) ∧
      IsConj (centralRepresentative i).val x.val := by
  obtain ⟨i,c,hc,he⟩ := involution_parabolic_conjugate_representative x hx
  refine ⟨i,?_,(isConj_iff.mpr ⟨c,he⟩).symm⟩
  rcases hc with hc | hc
  · have hcl : IsConj (inclusion (unipotent_le_borel.trans inf_le_left) x : pointParabolic (F := F))
        (inclusion inf_le_left (borelRepresentative i)) :=
      isConj_iff.mpr ⟨⟨c,hc⟩,Subtype.ext he⟩
    exact (f.map_isConj hcl).symm
  · have hcl : IsConj (inclusion (unipotent_le_borel.trans inf_le_right) x : planeParabolic (F := F))
        (inclusion inf_le_right (borelRepresentative i)) :=
      isConj_iff.mpr ⟨⟨c,hc⟩,Subtype.ext he⟩
    have hh := (g.map_isConj hcl).symm
    have hxg : f (inclusion (unipotent_le_borel.trans inf_le_left) x)=
        g (inclusion (unipotent_le_borel.trans inf_le_right) x) :=
      hag (inclusion unipotent_le_borel x)
    rw [hag,hxg]
    exact hh

end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
