module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing

/-!
# Finite transport at an incident marked flag

Choose the common representative of the two incident parabolic cosets inside
the first parabolic. Compose its inner conjugation with the original embedding
of the finite group M. This is an isomorphism onto the actual alpha stabilizer;
the unchanged marked Section 1 extension then maps to the two incident actors.
All inverse images below are in M, never in a fictitiously finite free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7), pp.847--848, and
(4.6.8), claim (3), p.906.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The original embedding in coordinates centered at the common flag representative. -/
def embedding (R : Subgroup M) (m : M) : M →* FreeAmalgam R :=
  (embedM R).comp (MulAut.conj m).toMonoidHom

@[simp] theorem embedding_apply (m x : M) :
    embedding R m x = embedM R m * embedM R x * (embedM R m)⁻¹ := by
  simp only [embedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]

theorem embedding_injective (m : M) : Function.Injective (embedding R m) :=
  (embedM_injective R).comp (MulAut.conj m).injective

theorem embedding_range (m : M) : (embedding R m).range = stabilizer R (alpha R) := by
  rw [alpha, stabilizer_m_base]
  change ((embedM R).comp (MulAut.conj m).toMonoidHom).range = (embedM R).range
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨MulAut.conj m y, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (MulAut.conj m).surjective y
    exact ⟨z, rfl⟩

/-- A genuine isomorphism from the finite source group to the local stabilizer. -/
noncomputable def stabilizerEquiv (m : M) : M ≃* stabilizer R (alpha R) :=
  (MonoidHom.ofInjective (embedding_injective (R := R) m)).trans
    (MulEquiv.subgroupCongr (embedding_range (R := R) m))

@[simp] theorem stabilizerEquiv_coe (m x : M) :
    (stabilizerEquiv (R := R) m x : FreeAmalgam R) = embedding R m x := rfl

/-- Inverse image through the actual finite stabilizer isomorphism. -/
def pull (m : M) (A : Subgroup (FreeAmalgam R)) : Subgroup M :=
  A.comap (embedding R m)

theorem map_pull (m : M) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) : (pull m A).map (embedding R m) = A :=
  map_comap_eq_self (by rwa [embedding_range])

theorem pull_map (m : M) (A : Subgroup M) :
    pull m (A.map (embedding R m)) = A :=
  comap_map_eq_self_of_injective (embedding_injective m) A

/-- Actual subgroup elements correspond, not merely their orders or family tags. -/
noncomputable def pullEquiv (m : M) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) : pull m A ≃* A :=
  ((pull m A).equivMapOfInjective (embedding R m) (embedding_injective m)).trans
    (MulEquiv.subgroupCongr (map_pull m A hA))

@[simp] theorem pullEquiv_coe (m : M) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) (x : pull m A) :
    (pullEquiv m A hA x : FreeAmalgam R) = embedding R m x := rfl

/-- Normality is needed only inside the finite alpha stabilizer. -/
theorem pull_normal (m : M) (A : Subgroup (FreeAmalgam R))
    (hA : stabilizer R (alpha R) ≤ normalizer A) : (pull m A).Normal := by
  constructor
  intro x hx g
  change embedding R m (g * x * g⁻¹) ∈ A
  rw [map_mul, map_mul, map_inv]
  apply (mem_normalizer_iff.mp (hA ?_) (embedding R m x)).mp hx
  rw [← embedding_range m]
  exact ⟨g, rfl⟩

/-- Transport relative normalization without asserting amalgam normality. -/
theorem pull_normalizes (m : M) (A P : Subgroup (FreeAmalgam R))
    (h : P ≤ normalizer A) : pull m P ≤ normalizer (pull m A) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  change embedding R m (g * x * g⁻¹) ∈ A
  rw [map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.mp (h hg) (embedding R m x)).mp hx

theorem pull_commutator (m : M) (A B : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) (hB : B ≤ stabilizer R (alpha R)) :
    pull m ⁅A, B⁆ = ⁅pull m A, pull m B⁆ := by
  apply map_injective (embedding_injective m)
  rw [map_commutator, map_pull m A hA, map_pull m B hB,
    map_pull m _ ((Subgroup.commutator_le_sup A B).trans (sup_le hA hB))]

theorem pull_sup (m : M) (A B : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) (hB : B ≤ stabilizer R (alpha R)) :
    pull m (A ⊔ B) = pull m A ⊔ pull m B := by
  apply map_injective (embedding_injective m)
  rw [Subgroup.map_sup, map_pull m A hA, map_pull m B hB,
    map_pull m _ (sup_le hA hB)]

/-- The fixed subgroup is pulled back with its actual commutator denominator. -/
theorem pull_commutatorPreimage (m : M) (A B N : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) (hB : B ≤ stabilizer R (alpha R))
    (hAN : A ≤ normalizer N) :
    pull m (commutatorPreimage A B N) =
      commutatorPreimage (pull m A) (pull m B) (pull m N) := by
  apply le_antisymm
  · apply le_commutatorPreimage (comap_mono (commutatorPreimage_le A B N))
    change ⁅pull m (commutatorPreimage A B N), pull m B⁆ ≤ pull m N
    rw [← pull_commutator m _ B ((commutatorPreimage_le A B N).trans hA) hB]
    exact comap_mono (commutator_commutatorPreimage_le A B N hAN)
  · apply map_le_iff_le_comap.mp
    apply le_commutatorPreimage
    · exact (map_mono (commutatorPreimage_le _ _ _)).trans_eq (map_pull m A hA)
    · have h := map_mono (f := embedding R m)
        (commutator_commutatorPreimage_le (pull m A) (pull m B) (pull m N)
          (pull_normalizes m N A hAN))
      rw [map_commutator, map_pull m B hB] at h
      exact h.trans (map_comap_le _ _)

/-- Natural rank-one coordinates, including their actual kernel and conjugation action,
transport through the finite stabilizer isomorphism. -/
noncomputable def pullRankOneFactor (m : M) (K H N : Subgroup (FreeAmalgam R))
    (hK : K ≤ stabilizer R (alpha R)) (hH : H ≤ stabilizer R (alpha R))
    (n : RankOnePairing.RankOneFactor K H N) :
    RankOnePairing.RankOneFactor (pull m K) (pull m H) (pull m N) where
  projection := n.projection.comp (pullEquiv m K hK).toMonoidHom
  surjective := n.surjective.comp (pullEquiv m K hK).surjective
  coordinates := n.coordinates.comp (pullEquiv m H hH).toMonoidHom
  coordinates_surjective := n.coordinates_surjective.comp (pullEquiv m H hH).surjective
  kernel := by
    ext x
    change (pullEquiv m H hH x) ∈ n.coordinates.ker ↔ embedding R m x ∈ N
    rw [n.kernel]
    rfl
  normalized := pull_normalizes m H K n.normalized
  action := by
    intro l x y hy
    apply n.action (pullEquiv m K hK l) (pullEquiv m H hH x) (pullEquiv m H hH y)
    change embedding R m (y : M) = embedding R m (l : M) *
      embedding R m (x : M) * (embedding R m (l : M))⁻¹
    rw [hy, map_mul, map_mul, map_inv]

/-- The intrinsic subgroup quotients are isomorphic under the same embedding. -/
noncomputable def pullQuotientEquiv (m : M) (H N : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R (alpha R)) (hHN : H ≤ normalizer N) :
    letI := normal_subgroupOf_of_le_normalizer hHN
    letI := normal_subgroupOf_of_le_normalizer (pull_normalizes m N H hHN)
    (pull m H) ⧸ (pull m N).subgroupOf (pull m H) ≃* H ⧸ N.subgroupOf H := by
  letI := normal_subgroupOf_of_le_normalizer hHN
  letI := normal_subgroupOf_of_le_normalizer (pull_normalizes m N H hHN)
  apply QuotientGroup.congr _ _ (pullEquiv m H hH)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, rfl⟩ := (pullEquiv m H hH).surjective x
    exact ⟨y, hx, rfl⟩

private theorem map_localGenerated {G : Type*} [Group G] (f : M →* G)
    (P X : Subgroup M) (hXP : X ≤ P) :
    (RankOnePairing.localGenerated P X).map f =
      RankOnePairing.localGenerated (P.map f) (X.map f) := by
  open RankOnePairing RankOnePairing.Incidence in
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply localGenerated_le_of_normalizes
      · exact ((map_le_iff_le_comap.mp (localGenerated_normalized (P.map f) (X.map f))).trans
          (le_normalizer_comap f))
      · exact map_le_iff_le_comap.mp (le_localGenerated _ _ (map_mono hXP))
    · apply localGenerated_le_of_normalizes
      · exact (map_mono (localGenerated_normalized P X)).trans (le_normalizer_map f)
      · exact map_mono (le_localGenerated P X hXP)

/-- Relative normal closure commutes with transport inside the actual local actor. -/
theorem map_pull_localGenerated (m : M) (P X : Subgroup (FreeAmalgam R))
    (hP : P ≤ stabilizer R (alpha R)) (hXP : X ≤ P) :
    (RankOnePairing.localGenerated (pull m P) (pull m X)).map (embedding R m) =
      RankOnePairing.localGenerated P X := by
  rw [map_localGenerated (embedding R m) (pull m P) (pull m X)
      (show pull m X ≤ pull m P from comap_mono hXP), map_pull m P hP,
    map_pull m X (hXP.trans hP)]

/-- Ambient normal closure in finite M is normal closure only in G_alpha after embedding. -/
theorem map_generated_pull (m : M) (X : Subgroup (FreeAmalgam R))
    (hX : X ≤ stabilizer R (alpha R)) :
    (RankOnePairing.generated (pull m X)).map (embedding R m) =
      RankOnePairing.localGenerated (stabilizer R (alpha R)) X := by
  have ht : RankOnePairing.localGenerated (⊤ : Subgroup M) (pull m X) =
      RankOnePairing.generated (pull m X) := by
    apply le_antisymm (RankOnePairing.localGenerated_le_generated _ _)
    let : (RankOnePairing.localGenerated (⊤ : Subgroup M) (pull m X)).Normal :=
      normalizer_eq_top_iff.mp (top_unique
        (RankOnePairing.Incidence.localGenerated_normalized _ _))
    apply normalClosure_le_normal
    exact RankOnePairing.le_localGenerated _ _ le_top
  rw [← ht, map_localGenerated _ _ _ le_top, ← MonoidHom.range_eq_map,
    embedding_range m, map_pull m X hX]

/-- The embedding intertwines conjugation on every subgroup. -/
theorem map_embedding (m : M) (A : Subgroup M) :
    A.map (embedding R m) = localConjugate (A.map (embedM R)) m := by
  rw [localConjugate, map_map]
  congr 1
  ext x
  exact embedding_apply m x

/-- A common representative of the two incident cosets, chosen in the first parabolic. -/
noncomputable def representative (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) : M :=
  Classical.choose ((flagIncident_one_iff source i d).mp hd)

theorem representative_mem (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    representative source i d hd ∈ parabolic source.projection source.flag i :=
  (Classical.choose_spec ((flagIncident_one_iff source i d).mp hd)).1

theorem representative_right (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    d⁻¹ * representative source i d hd ∈ parabolic source.projection source.flag (!i) :=
  (Classical.choose_spec ((flagIncident_one_iff source i d).mp hd)).2

variable [Finite M]

/-- The original finite extension, with its original projection and common Sylow. -/
noncomputable abbrev extension (source : LocalSource L R) : RankOnePairing.Extension (M := M) :=
  pairingExtension source

/-- The first marked full actor is fixed by this choice of coordinates. -/
theorem map_first_actor (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (RankOnePairing.localParabolic (extension source) i).map
      (embedding R (representative source i d hd)) = flagParabolic source i := by
  rw [pairing_parabolic, map_embedding]
  exact mem_normalizer_iff_map_conj_eq.mp ((flagParabolic source i).le_normalizer
    (mem_map_of_mem (embedM R) (representative_mem source i d hd)))

/-- The opposite marked full actor is the actual incident actor represented by d. -/
theorem map_second_actor (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (RankOnePairing.localParabolic (extension source) (!i)).map
      (embedding R (representative source i d hd)) = localFlagActor source (!i) d := by
  rw [pairing_parabolic, map_embedding]
  change localFlagActor source (!i) (representative source i d hd) = _
  simpa only [mul_inv_cancel_left] using localFlagActor_right_mul source (!i) d
    (d⁻¹ * representative source i d hd) (representative_right source i d hd)

/-- The first selected two-core retains the actual first flag kernel. -/
theorem map_first_core (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (RankOnePairing.selectedCore (extension source) i).map
      (embedding R (representative source i d hd)) = flagKernel source i := by
  rw [map_embedding, pairing_selectedCore]
  exact mem_normalizer_iff_map_conj_eq.mp (flagKernel_normalized source i
    (mem_map_of_mem (embedM R) (representative_mem source i d hd)))

/-- The opposite selected two-core is the actual translated kernel. -/
theorem map_second_core (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (RankOnePairing.selectedCore (extension source) (!i)).map
      (embedding R (representative source i d hd)) = localFlagKernel source (!i) d := by
  rw [map_embedding, pairing_selectedCore]
  change localFlagKernel source (!i) (representative source i d hd) = _
  simpa only [mul_inv_cancel_left] using localFlagKernel_right_mul source (!i) d
    (d⁻¹ * representative source i d hd) (representative_right source i d hd)

/-- The first tilded residual is kept separate from the full actor. -/
theorem map_first_residual (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (rankOne (RankOnePairing.localParabolic (extension source) i)).map
      (embedding R (representative source i d hd)) = flagResidual source i := by
  rw [pairing_parabolic, map_embedding]
  exact mem_normalizer_iff_map_conj_eq.mp (flagResidual_normalized source i
    (mem_map_of_mem (embedM R) (representative_mem source i d hd)))

/-- The second tilded residual is exactly the one in the hypothetical triple. -/
theorem map_second_residual (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    (rankOne (RankOnePairing.localParabolic (extension source) (!i))).map
      (embedding R (representative source i d hd)) = localFlagResidual source (!i) d := by
  rw [pairing_parabolic, map_embedding]
  change localFlagResidual source (!i) (representative source i d hd) = _
  simpa only [mul_inv_cancel_left] using localFlagResidual_right_mul source (!i) d
    (d⁻¹ * representative source i d hd) (representative_right source i d hd)

/-- Pulling the literal incident seed into M gives precisely the required relative normality. -/
theorem seed_normal (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    ((pull (representative source i d hd) (Pairing.seed source i d)).subgroupOf
      (RankOnePairing.localParabolic (extension source) (!i))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  have h := pull_normalizes (representative source i d hd) _ _
    (Pairing.seed_normalized source geometry hlarge i hkernel d hd htriple)
  rw [← map_second_actor source i d hd, pull_map] at h
  exact h

/-- The extension kernel maps to the genuine alpha two-core. -/
theorem map_extension_core (source : LocalSource L R) (m : M) :
    (RankOnePairing.extensionCore (extension source).projection).map (embedding R m) =
      Q R (alpha R) := by
  rw [pairingExtension_projection, pairing_core, source.projection_kernel,
    embedding, ← map_map, MulEquiv.toMonoidHom_eq_coe, Normal.map_conj_eq]
  exact (Q_alpha R source.two_group source.core_le).symm

/-- The global component maps to the actual tilded alpha residual. -/
theorem map_component (source : LocalSource L R) (m : M) :
    (RankOnePairing.component (extension source).projection (extension source).flag).map
      (embedding R m) = Ltilde R (alpha R) := by
  rw [pairingExtension_projection, pairingExtension_flag, RankOnePairing.component,
    source.rank_one_generation, ← source.residual, embedding, ← map_map, MulEquiv.toMonoidHom_eq_coe, Normal.map_conj_eq]
  exact (Ltilde_alpha R).symm

/-- The natural flag section is transported with the tilded residual as its denominator actor. -/
noncomputable def firstNatural (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (natural : FlagNaturalSection source i)
    (d : M) (hd : flagIncident source i 1 d) :
    let m := representative source i d hd
    RankOnePairing.RankOneFactor (RankOnePairing.localParabolic (extension source) i)
      (pull m (V R (beta R)))
      (commutatorPreimage (pull m (V R (beta R)))
        (rankOne (RankOnePairing.localParabolic (extension source) i))
        (pull m (Z R (alpha R)))) := by
  let m := representative source i d hd
  have hV : V R (beta R) ≤ stabilizer R (alpha R) :=
    (edgeRadius_le_radius _ _ rfl (base_adjacent R)).trans (geometry.V_local _ rfl hlarge)
  have n := pullRankOneFactor m _ _ _ (flagParabolic_le source i) hV natural
  rw [← map_first_actor source i d hd, pull_map] at n
  rw [pull_commutatorPreimage m _ _ _ hV
    ((flagResidual_le source i).trans (flagParabolic_le source i))
    (hV.trans (Z_normalized R _)), ← map_first_residual source i d hd, pull_map] at n
  exact n

/-- The original natural three-space, with the coordinate change induced by m. -/
noncomputable def naturalCoordinates (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (m : M) :
    RankOnePairing.NaturalFactor source.projection ⊤ (pull m (U R (alpha R))) ⊥ := by
  let e := pullEquiv m (U R (alpha R)) ((DistanceEight.U_le_Z R _).trans (Z_le_stabilizer R _))
  let c := e.trans common.natural.equiv
  letI := pull_normal m (U R (alpha R)) (U_normalized _)
  refine {
    marking := (MulAut.conj (source.projection m)).trans common.natural.marking
    coordinates := c.toMonoidHom
    surjective := c.surjective
    kernel := ?_
    normalized := le_normalizer_of_normal
    action := ?_ }
  · rw [bot_subgroupOf]
    exact c.toMonoidHom.ker_eq_bot_iff.mpr c.injective
  · intro l _ x y hy
    have hc := common.natural.action (m * l * m⁻¹) (e x) (e y) (by
      change embedding R m (y : M) = embedM R (m * l * m⁻¹) *
        embedding R m (x : M) * (embedM R (m * l * m⁻¹))⁻¹
      change embedding R m (y : M) = embedding R m l *
        embedding R m (x : M) * (embedding R m l)⁻¹
      rw [hy, map_mul, map_mul, map_inv])
    simpa only [c, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_inv, MulEquiv.trans_apply, MulAut.conj_apply] using hc

/-- The finite seed's ambient normal closure maps to precisely the source span. -/
theorem map_generated_seed (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    (RankOnePairing.generated
      (pull (representative source i d hd) (Pairing.seed source i d))).map
      (embedding R (representative source i d hd)) = Pairing.span source i d :=
  map_generated_pull _ _ ((Pairing.seed_le_Q source geometry hlarge i hkernel d hd).trans
    (fun _ hx => hx.1))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport
