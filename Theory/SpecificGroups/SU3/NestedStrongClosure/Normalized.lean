module

public import Theory.SpecificGroups.SU3.NestedStrongClosure.Actors
public import Theory.SpecificGroups.SU3.NestedStrongClosure.Displacements
public import Theory.SpecificGroups.SU3.ExtensionBorel
public import Theory.GroupTheory.SetStrongClosureImage

/-!
# Strong closure in a root-containing unitary two-subgroup

Pull back the strongly closed subgroup through the literal inner embedding
and the projective root map. Full-torus fusion makes this pullback either
central or the whole root. In the central case, normality inside the given
two-subgroup makes all root displacements square to one, so the field
parameter vanishes and odd diagonal order forces innerness. In the full-root
case, the diagonal-field involution calculation excludes outer elements.
Sylow maximality identifies the inner intersection with the same root Sylow,
which proves preservation of the root by every actor used in the calculation.

Source: Huppert II.10.12; GLS3 Theorem 2.5.12 and Section 2.7; the unitary
terminal case of Aschbacher (1975), Lemma 3.4, printed pp.94–96.
-/

public section
open Matrix Subgroup BenderSuzuki.External Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
open BorelTorus BorelTorus.SemilinearActors ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private theorem innerEmbedding_conj {G : Type*} [Group G]
    (K : Subgroup (MulAut G)) (hK : MulAut.innerSubgroup G ≤ K)
    (a : K) (x : G) :
    innerEmbedding K hK (a.val x) = a * innerEmbedding K hK x * a⁻¹ := by
  apply Subtype.ext
  ext y
  simp [innerEmbedding, MulAut.conj_apply]

/-- A strongly closed subgroup of a two-subgroup containing the inner root
is inner if all of its involutions are inner. -/
theorem normalized_inner_of_involutions {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ K)
    (T B : Subgroup K) (hT : IsPGroup 2 T)
    (hroot : (projectiveRoot J hJ).map (innerEmbedding K hK) ≤ T)
    (hB : B ≤ T) (hc : IsStronglyClosedSet (B : Set K) T ⊤)
    (hi : ∀ a ∈ B, a^2 = 1 → a.val ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    B.map K.subtype ≤ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let f := innerEmbedding K hK
  have hconj := huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed
  have hf : Function.Injective f := innerEmbedding_injective K hK
    (binary_inner_injective J hJ (by omega) hcard hconj)
  let P := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  have hpre : T.comap f = projectiveRoot J hJ :=
    P.is_maximal' (hT.comap_of_injective f hf) (Subgroup.map_le_iff_le_comap.mp hroot)
  have hstable (a : K) (ha : a ∈ T) :
      (projectiveRoot J hJ).map a.val.toMonoidHom = projectiveRoot J hJ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hpre]
      change f (a.val x) ∈ T
      rw [innerEmbedding_conj]
      exact T.mul_mem (T.mul_mem ha (hroot (mem_map_of_mem f hx))) (T.inv_mem ha)
    · exact le_of_eq (Subgroup.card_map_of_injective a.val.injective).symm
  let u := hermitianUnipotentPSU J hJ
  let W := B.comap (f.comp u)
  have htorus (k : Eˣ) (z : hermitianUnipotentCoord J) (hz : z ∈ W) :
      hermitianTorusAction J k z ∈ W := by
    have he : f (u (hermitianTorusAction J k z)) =
        f (hermitianTorusPSU J hJ k) * f (u z) * (f (hermitianTorusPSU J hJ k))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg f (EvenInner.projective_torus_action J hJ k z).symm
    change f (u (hermitianTorusAction J k z)) ∈ B
    rw [he]
    apply hc.2 (f (u z)) hz (f (hermitianTorusPSU J hJ k))⁻¹ (mem_top _)
    · simpa only [inv_inv, ← he] using
        hroot (mem_map_of_mem f (show u (hermitianTorusAction J k z) ∈ projectiveRoot J hJ from ⟨_, rfl⟩))
  have hq : 2 < 2^n := lt_of_lt_of_le (by decide : 2 < 2^2)
    (Nat.pow_le_pow_right (by decide) hn)
  rcases BinaryRootFrattini.invariant_subgroup J hcard hfixed hq W htorus with hsmall | hfull
  · have hsquare (x : ProjectiveSpecialUnitaryMatrixGroup J)
        (hx : x ∈ projectiveRoot J hJ) (hxb : f x ∈ B) : x^2 = 1 := by
      obtain ⟨z, rfl⟩ := hx
      have hz : z^2 = 1 := (BinaryRootFrattini.mem_frattini_iff_square_one J hcard hfixed z).mp (hsmall hxb)
      rw [← map_pow, hz, map_one]
    rintro _ ⟨a, ha, rfl⟩
    have hd (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : x ∈ projectiveRoot J hJ) :
        (a.val x * x⁻¹)^2 = 1 := by
      have hfx : f x ∈ T := hroot (mem_map_of_mem f hx)
      have hax : a.val x ∈ projectiveRoot J hJ := by
        rw [← hstable a (hB ha)]
        exact mem_map_of_mem _ hx
      apply hsquare _ ((projectiveRoot J hJ).mul_mem hax ((projectiveRoot J hJ).inv_mem hx))
      rw [map_mul, map_inv, innerEmbedding_conj]
      have hh : f x * a⁻¹ * (f x)⁻¹ ∈ B := by
        have hh := hc.2 a⁻¹ (B.inv_mem ha) (f x)⁻¹ (mem_top _)
          (by simpa only [inv_inv] using
            T.mul_mem (T.mul_mem hfx (T.inv_mem (hB ha))) (T.inv_mem hfx))
        simpa only [inv_inv, SetLike.mem_coe] using hh
      simpa only [mul_assoc] using B.mul_mem ha hh
    obtain ⟨σ, hσ⟩ := J.semilinear_coverage n hn hJ hcard hfixed a.val
    have hs := field_eq_one_of_root_square_displacements J hJ hcard hfixed
      a.val σ hσ (hstable a (hB ha)) hd
    rw [hs] at hσ
    obtain ⟨v, hv⟩ := hσ
    obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed
      a.val 1 v hv (hstable a (hB ha))
    have hroot' : (projectiveRoot J hJ).map MulAut.conj ≤ T.map K.subtype := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨f x, hroot (mem_map_of_mem f hx), rfl⟩
    obtain ⟨x, _, hx⟩ := projective_identity_field_mem_root_inner J hJ hcard (by omega)
      (T.map K.subtype) (hT.map _) hroot' a.val (mem_map_of_mem _ (hB ha)) v
      h10 h20 h21 (fun x => by
        simpa only [show (1 : E ≃+* E).toRingHom = RingHom.id E from rfl,
          ProjGenLinGroup.map_id, MonoidHom.id_apply] using hv x)
    exact ⟨x, hx⟩
  · have hrootB : (projectiveRoot J hJ).map MulAut.conj ≤ B.map K.subtype := by
      rintro _ ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨f (u z), (show z ∈ W from hfull ▸ mem_top z), rfl⟩
    apply root_containing_inner_of_involutions J hn hJ hcard hfixed
      (B.map K.subtype) ((hT.to_le hB).map _) hrootB
    · rintro _ ⟨a, ha, rfl⟩
      exact hstable a (hB ha)
    · rintro _ ⟨a, ha, rfl⟩ hs
      exact hi a ha (Subtype.ext hs)

end BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
