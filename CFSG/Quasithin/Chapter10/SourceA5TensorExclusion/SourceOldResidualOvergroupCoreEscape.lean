module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaChief
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import Theory.GroupTheory.SylowLocalCore

/-!
# The opposite Sylow factor in the original tensor branch

Normal restriction identifies the literal Sylow intersection T ∩ L. Its
A₅ quotient has even order, so this intersection contains an element with
nontrivial quotient image. Conjugating by any element of T outside N_T(L)
puts that element in the other component. The exact two-factor quotient
markings show that it cannot also belong to L.

Consequently neither T ∩ L₀ nor the original common subgroup
S = (T ∩ L₀) O₂(L₀T) is contained in L. This is the terminal noncontainment
used in the core-zero weak BN-pair branch of 9.3.3. No generation-one or
point-Sylow hypothesis is used.

Source: Aschbacher–Smith 9.3.3, combined manuscript of 1 March 2004,
printed p.733, with the original two-factor quotient from D.3.5–7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- Normal Sylow restriction gives the actual component Sylow T ∩ L. -/
theorem old_residual_component_sylow : ∃ P : Sylow 2 L,
    (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
  let M := normalizer (localOrbit T L : Set G)
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  obtain ⟨P,hP⟩ := (T.subtype hTM).exists_map_subtype_eq_inf_of_normalizes
    (localOrbit T L).le_normalizer (show M ≤ normalizer (localOrbit T L : Set G) from le_rfl)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] at hP
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_inf_of_normalizes (le_componentOrbit L T)
    (source_nonnormal_orbit_le_normalizer D m.sylow_not_normalizes_component)
  refine ⟨Q,?_⟩
  rw [hP,inf_assoc,inf_eq_right.mpr (le_componentOrbit L T)] at hQ
  exact hQ

/-- The opposite Sylow factor contains an element outside the original component. -/
theorem old_residual_opposite_sylow_escape
    {u : G} (hu : u ∈ (T : Subgroup G)) (huN : u ∉ normalizer (L : Set G)) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∈ L.map (MulAut.conj u).toMonoidHom ∧ t ∉ L := by
  obtain ⟨P,hP⟩ := m.old_residual_component_sylow
  let f : L →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective hf
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have htwo : 2 ∣ Nat.card R := by
    apply (Nat.prime_two.dvd_mul.mp ?_).resolve_right R.not_dvd_index
    rw [(R : Subgroup (alternatingGroup (Fin 5))).card_mul_index,hcard]
    norm_num
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 htwo
  obtain ⟨l,hl,hlr⟩ := r.property
  have hlT : (l : G) ∈ (T : Subgroup G) := (hP.le (mem_map_of_mem _ hl)).1
  let t := u * (l : G) * u⁻¹
  refine ⟨t,(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hu hlT)
    ((T : Subgroup G).inv_mem hu),mem_map.mpr ⟨l,l.property,rfl⟩,?_⟩
  intro htL
  obtain ⟨q,_,_,hfirst,hsecond⟩ := source_a5_original_product_quotient D e
    m.sylow_not_normalizes_component hu huN
  have hh := congrArg Prod.snd ((hsecond l).symm.trans (hfirst ⟨t,htL⟩))
  change f l = 1 at hh
  have hr1 : r = 1 := Subtype.ext (hlr.symm.trans hh)
  simp only [hr1,orderOf_one] at hr
  omega

/-- The common Sylow subgroup of the two original factors is not contained in L. -/
theorem old_residual_orbit_sylow_not_le_component :
    ¬ (T : Subgroup G) ⊓ localOrbit T L ≤ L := by
  obtain ⟨u,hu,huN⟩ := SetLike.not_le_iff_exists.mp m.sylow_not_normalizes_component
  obtain ⟨t,htT,htB,htL⟩ := m.old_residual_opposite_sylow_escape hu huN
  have hBR : L.map (MulAut.conj u).toMonoidHom ≤ localOrbit T L :=
    le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨u,hu⟩
  exact fun h => htL (h ⟨htT,hBR htB⟩)

/-- The common subgroup S of original 9.3.2–3 is not contained in L. -/
theorem old_residual_common_sylow_not_le_component :
    ¬ (((T : Subgroup G) ⊓ localOrbit T L) ⊔ (localJoin T L).pCoreIn 2) ≤ L := by
  intro h
  exact m.old_residual_orbit_sylow_not_le_component (le_sup_left.trans h)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
