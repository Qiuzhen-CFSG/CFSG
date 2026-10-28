module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The literal central quotient in MS93 (4.6.9)

The denominator is Z_a intersected with the intrinsic center of G_a,
computed inside G_a and then embedded into the free amalgam. Bzero is the
preimage in V_a of the centralizer of its image in that quotient. Its
membership and normalization lemmas preserve the actual quotient map.

The marked triple bound puts [V_beta,Ltilde_delta1] in Bzero. Consequently
the residual normalizes each edge sublayer joined with Bzero, the first
step of the printed displacement argument. The reverse containment of
Bzero in the radius center is not asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The actual denominator in the local quotient defining source B₀. -/
noncomputable def centralDenominator (a : Vertex R) : Subgroup (stabilizer R a) :=
  (Z R a).subgroupOf (stabilizer R a) ⊓ center (stabilizer R a)

theorem centralDenominator_normal (geometry : Geometry R) (a : Vertex R) :
    (centralDenominator a).Normal := by
  let := geometry.Z_normal a
  exact Subgroup.normal_inf_normal _ _

/-- Source B₀, using the quotient of G_a by Z_a ∩ Z(G_a). -/
noncomputable def Bzero (geometry : Geometry R) (a : Vertex R) : Subgroup (FreeAmalgam R) :=
  letI := centralDenominator_normal geometry a
  (centralizerModulo ((V R a).subgroupOf (stabilizer R a))
    ((V R a).subgroupOf (stabilizer R a)) (centralDenominator a)).map
      (stabilizer R a).subtype

open scoped commutatorElement in
theorem mem_Bzero_iff (geometry : Geometry R) (a : Vertex R)
    (hV : V R a ≤ stabilizer R a) (x : FreeAmalgam R) :
    x ∈ Bzero geometry a ↔ x ∈ V R a ∧ ∀ v ∈ V R a,
      ⁅v, x⁆ ∈ Z R a ⊓ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  let := centralDenominator_normal geometry a
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxV, hc⟩ := mem_centralizerModulo_iff.mp hx
    refine ⟨hxV, ?_⟩
    intro v hv
    have hh := hc ⟨v, hV hv⟩ hv
    exact ⟨hh.1, ⟨_, hh.2, rfl⟩⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hV hx⟩, mem_centralizerModulo_iff.mpr ⟨hx, ?_⟩, rfl⟩
    intro v hv
    have hh := hc v hv
    refine ⟨hh.1, ?_⟩
    obtain ⟨z, hz, he⟩ := hh.2
    exact (show z = ⁅v, (⟨x, hV hx⟩ : stabilizer R a)⁆ from Subtype.ext he) ▸ hz

theorem Bzero_le_radius (geometry : Geometry R) (a : Vertex R) :
    Bzero geometry a ≤ V R a := by
  let := centralDenominator_normal geometry a
  exact (map_mono (centralizerModulo_le _ _ _)).trans
    (by rw [subgroupOf_map_subtype]; exact inf_le_left)

theorem flag_commutator_le_Bzero [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ⁅V R (beta R), flagResidual source i⁆ ≤ Bzero geometry (alpha R) := by
  have he := (flag_commutator_le_edgeRadius source geometry hlarge i hkernel).trans
    (edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R))
  have hV := geometry.V_local (alpha R) rfl hlarge
  have hZ : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤ Z R (alpha R) :=
    (commutator_mono he (V_le_Q geometry hlarge (alpha R) rfl)).trans
      (early.commutator_le_Z (alpha R) rfl)
  intro x hx
  apply (mem_Bzero_iff geometry (alpha R) hV x).mpr
  refine ⟨he hx, ?_⟩
  intro v hv
  have hc := commutator_mem_commutator hv hx
  rw [commutator_comm] at hc
  exact ⟨hZ hc, htriple hc⟩

/-- The embedded denominator is literally Z_a intersected with Z(G_a). -/
theorem centralDenominator_map (a : Vertex R) :
    (centralDenominator a).map (stabilizer R a).subtype =
      Z R a ⊓ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  rw [centralDenominator, map_inf _ _ _ (stabilizer R a).subtype_injective,
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)]

/-- The commutator characterization of the source quotient centralizer. -/
theorem le_Bzero_iff (geometry : Geometry R) (a : Vertex R)
    (hV : V R a ≤ stabilizer R a) (D : Subgroup (FreeAmalgam R)) :
    D ≤ Bzero geometry a ↔ D ≤ V R a ∧
      ⁅D, V R a⁆ ≤ Z R a ⊓ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  constructor
  · intro h
    refine ⟨h.trans (Bzero_le_radius geometry a), ?_⟩
    rw [commutator_comm]
    exact commutator_le.mpr fun v hv x hx =>
      ((mem_Bzero_iff geometry a hV x).mp (h hx)).2 v hv
  · rintro ⟨h, hc⟩ x hx
    apply (mem_Bzero_iff geometry a hV x).mpr
    refine ⟨h hx, ?_⟩
    intro v hv
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator hv hx)

/-- The radius center lies in B₀ before the reverse containment is known. -/
theorem radius_center_le_Bzero (geometry : Geometry R) (a : Vertex R)
    (hV : V R a ≤ stabilizer R a) :
    (center (V R a)).map (V R a).subtype ≤ Bzero geometry a := by
  apply (le_Bzero_iff geometry a hV _).mpr
  refine ⟨map_subtype_le _, ?_⟩
  have hc : (center (V R a)).map (V R a).subtype ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    rintro x ⟨z, hz, rfl⟩ v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v, hv⟩)
  rw [commutator_eq_bot_iff_le_centralizer.mpr hc]
  exact bot_le

/-- Every local conjugation preserves the literal quotient centralizer B₀. -/
theorem Bzero_normalized (geometry : Geometry R) (a : Vertex R)
    (hV : V R a ≤ stabilizer R a) :
    stabilizer R a ≤ normalizer (Bzero geometry a : Set (FreeAmalgam R)) := by
  let N := Z R a ⊓ (center (stabilizer R a)).map (stabilizer R a).subtype
  have hN : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    dsimp only [N]
    rw [← centralDenominator_map]
    let := centralDenominator_normal geometry a
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp (by
      have heq : ((centralDenominator a).map (stabilizer R a).subtype).subgroupOf
          (stabilizer R a) = centralDenominator a :=
        comap_map_eq_self_of_injective (stabilizer R a).subtype_injective _
      rw [heq]
      infer_instance)
  have hVN : V R a ≤ normalizer (N : Set (FreeAmalgam R)) := hV.trans hN
  have heq : Bzero geometry a = commutatorPreimage (V R a) (V R a) N := by
    apply le_antisymm
    · exact le_commutatorPreimage (Bzero_le_radius geometry a)
        ((le_Bzero_iff geometry a hV _).mp le_rfl).2
    · exact (le_Bzero_iff geometry a hV _).mpr
        ⟨commutatorPreimage_le _ _ _, commutator_commutatorPreimage_le _ _ _ hVN⟩
  rw [heq]
  exact commutatorPreimage_normalized _ _ _ _ hVN
    (DistanceEight.V_normalized R a) (DistanceEight.V_normalized R a) hN

/-- The triple bound already normalizes every edge sublayer modulo B₀. -/
theorem flag_normalizes_sup_Bzero [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (D : Subgroup (FreeAmalgam R)) (hD : D ≤ V R (beta R)) :
    flagResidual source i ≤ normalizer ((D ⊔ Bzero geometry (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hB := Bzero_normalized geometry (alpha R)
    (geometry.V_local (alpha R) rfl hlarge)
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hgB := hB ((flagResidual_le source i).trans (flagParabolic_le source i) hg)
  have hDconj : D.map (MulAut.conj g).toMonoidHom ≤ D ⊔ Bzero geometry (alpha R) := by
    rintro _ ⟨d, hd, rfl⟩
    have hc : ⁅g, d⁆ ∈ Bzero geometry (alpha R) := by
      have he := flag_commutator_le_Bzero source geometry hlarge early i hkernel htriple
      rw [commutator_comm] at he
      exact he (commutator_mem_commutator hg (hD hd))
    change (MulAut.conj g) d ∈ D ⊔ Bzero geometry (alpha R)
    rw [conj_eq_commutatorElement_mul]
    exact (D ⊔ Bzero geometry (alpha R)).mul_mem (mem_sup_right hc) (mem_sup_left hd)
  have hmap : (D ⊔ Bzero geometry (alpha R)).map (MulAut.conj g).toMonoidHom ≤
      D ⊔ Bzero geometry (alpha R) := by
    have hBmap : (Bzero geometry (alpha R)).map (MulAut.conj g).toMonoidHom =
        Bzero geometry (alpha R) := mem_normalizer_iff_map_conj_eq.mp hgB
    rw [Subgroup.map_sup, hBmap]
    exact sup_le hDconj le_sup_right
  exact hmap (mem_map_of_mem _ hx)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
