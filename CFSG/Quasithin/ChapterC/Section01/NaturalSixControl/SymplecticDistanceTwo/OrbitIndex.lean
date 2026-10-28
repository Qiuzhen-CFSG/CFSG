module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitFaithful
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Literal image and fixed-index transport for the critical orbit

The opposite graph subgroup is pulled back through the injective native
vertex embedding. Its permutation image has the original relative order,
and the commutator-preimage index is exactly the fixed-space index of the
faithful orbit action. Neighbor transitivity conjugates the edge image to
the specified elementary group of order eight. Every quotient map and actor
in these calculations is the original source map.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

private theorem commutatorPreimage_map_injective
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (A E Z : Subgroup G) (hn : A ≤ normalizer (Z : Set G)) :
    (commutatorPreimage A E Z).map f =
      commutatorPreimage (A.map f) (E.map f) (Z.map f) := by
  have hnf : A.map f ≤ normalizer (Z.map f : Set H) :=
    (map_mono hn).trans (le_normalizer_map f)
  apply le_antisymm
  · apply le_commutatorPreimage (map_mono (commutatorPreimage_le A E Z))
    rw [←map_commutator]
    exact map_mono (commutator_commutatorPreimage_le A E Z hn)
  · let D := commutatorPreimage (A.map f) (E.map f) (Z.map f)
    have hDr : D ≤ f.range := (commutatorPreimage_le _ _ _).trans (map_le_range f A)
    have hDm : (D.comap f).map f = D := map_comap_eq_self hDr
    have hDA : D.comap f ≤ A := by
      have hh := comap_mono (f := f) (commutatorPreimage_le (A.map f) (E.map f) (Z.map f))
      simpa only [comap_map_eq_self_of_injective hf] using hh
    have hDc : ⁅D.comap f,E⁆ ≤ Z := by
      apply (map_le_map_iff_of_injective hf).mp
      rw [map_commutator,hDm]
      exact commutator_commutatorPreimage_le _ _ _ hnf
    change D ≤ _
    rw [←hDm]
    exact map_mono (le_commutatorPreimage hDA hDc)

variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
  {c b : Vertex R}
  (hb : s.geometry.b R = 2)
  (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
  (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
  [IsElementaryAbelian 2 (OrbitQuotient R c b)]

def orbitActorImage (B : Subgroup (FreeAmalgam R)) : Subgroup S :=
  (B.comap (embedM R)).map s.projection

theorem orbit_edge_image_conjugate {e : Vertex R} (hae : Adjacent R (alpha R) e) :
    ∃ m : M, s.orbitActorImage (Q R e) =
      (R.map s.projection).map (MulAut.conj ((s.projection m)⁻¹)).toMonoidHom := by
  obtain ⟨g,hg,hge⟩ := stabilizer_transitive_neighbors R (alpha R) (base_adjacent R) hae
  rw [show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R] at hg
  obtain ⟨m,rfl⟩ := hg
  have hQe : Q R e = (R.map (MulAut.conj (m⁻¹)).toMonoidHom).map (embedM R) := by
    rw [←hge,Q_act,show Q R (hVertex R 1) = R.map (embedM R) from Q_beta R,
      map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (embedM R m)⁻¹ * embedM R x * ((embedM R m)⁻¹)⁻¹ =
      embedM R (m⁻¹*x*(m⁻¹)⁻¹)
    simp only [map_mul,map_inv]
  refine ⟨m,?_⟩
  change ((Q R e).comap (embedM R)).map s.projection = _
  rw [hQe,comap_map_eq_self_of_injective (embedM_injective R),map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change s.projection (m⁻¹*x*(m⁻¹)⁻¹) =
    (s.projection m)⁻¹ * s.projection x * ((s.projection m)⁻¹)⁻¹
  simp only [map_mul,map_inv]

theorem orbit_edge_image_card (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    {e : Vertex R} (hae : Adjacent R (alpha R) e) :
    Nat.card (s.orbitActorImage (Q R e)) = 8 := by
  obtain ⟨m,hm⟩ := s.orbit_edge_image_conjugate hae
  rw [hm,card_map_of_injective (MulAut.conj ((s.projection m)⁻¹)).injective,hfull,
    card_map_of_injective (MulAut.conj t).injective,pointCore_card]

theorem orbit_edge_image_elementary (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    {e : Vertex R} (hae : Adjacent R (alpha R) e) :
    IsElementaryAbelian 2 (s.orbitActorImage (Q R e)) := by
  obtain ⟨m,hm⟩ := s.orbit_edge_image_conjugate hae
  rw [hm,hfull]
  let := pointCore_elementary
  let := IsElementaryAbelian.map (p := 2) (A := pointCore)
    (MulAut.conj t).toMonoidHom
  exact IsElementaryAbelian.map _

theorem orbitActorImage_card (B : Subgroup (FreeAmalgam R))
    (hB : B ≤ stabilizer R (alpha R)) :
    Nat.card (s.orbitActorImage B) = (Q R (alpha R)).relIndex B := by
  have hBm : (B.comap (embedM R)).map (embedM R) = B := map_comap_eq_self
    (hB.trans_eq (stabilizer_m_base R))
  rw [orbitActorImage,←relIndex_ker,s.projection_kernel]
  have he := relIndex_map_map_of_injective (pCore 2 M) (B.comap (embedM R))
    (embedM_injective R)
  rw [hBm,←Q_alpha R s.two_group s.core_le] at he
  exact he.symm

theorem orbit_fixed_index (hsurj : Function.Surjective s.projection)
    (B : Subgroup (FreeAmalgam R)) (hB : B ≤ stabilizer R (alpha R)) :
    (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
      (criticalOrbit R c b) =
      2 ^ fixedCodim (s.orbitFullRepresentation hb hc hab hcb hsurj) (s.orbitActorImage B) := by
  have hBm : (B.comap (embedM R)).map (embedM R) = B := map_comap_eq_self
    (hB.trans_eq (stabilizer_m_base R))
  have hZm : (orbitLayer R).map (embedM R) = Z R (alpha R) := map_comap_eq_self
    ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hCm := commutatorPreimage_map_injective (embedM R) (embedM_injective R)
    (criticalOrbitNative R c b) (B.comap (embedM R)) (orbitLayer R)
    le_normalizer_of_normal
  rw [hBm,hZm] at hCm
  simp only [criticalOrbit]
  rw [←hCm,relIndex_map_map_of_injective _ _ (embedM_injective R)]
  have hi := BinaryConjugationSection.fixed_index_image _ _
    (s.orbitFullSection hb hc hab hcb hsurj) (B.comap (embedM R)) le_top
  rw [←map_map,map_subgroupOf_eq_of_le (show B.comap (embedM R) ≤ ⊤ from le_top)] at hi
  exact hi

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
