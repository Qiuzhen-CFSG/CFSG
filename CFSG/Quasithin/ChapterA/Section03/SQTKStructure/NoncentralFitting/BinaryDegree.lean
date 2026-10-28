module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryCoprimeDegree.PerfectPlane
/-!
# Faithful binary degree of the noncentral-Fitting C-component

The genuine A.3.6 source theorem supplies the actual odd omega subgroup and
its irreducible action. If this subgroup is elementary of order p², its
Frattini subgroup is trivial and the perfect-plane orbit bound gives degree
at least 15. If it is extraspecial of order p³, the existing faithful binary
degree theorem gives at least 20. The original SQTK hypotheses, component,
representation and omega action are retained in both cases.

The final corollary discharges the noncentral-Fitting alternative in the
C.5.12 pair-span argument once its faithful action has degree at most twelve.
Source: Aschbacher–Smith A.3.6, printed pp.43–45; C.5.12, printed p.163.
-/

public section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
universe u
variable {G : Type u} [Group G] [Finite G] {D : Subgroup G}

private theorem omega_irreducible_of_elementary
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p (omegaCore p K)]
    (hi : ∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
      (∀ g x, x∈A → omegaFrattiniAction p K g x∈A) → A=⊥ ∨ A=⊤) :
    ∀ A : Subgroup (omegaCore p K),
      (∀ g x, x∈A → MulAut.conjNormal g x∈A) → A=⊥ ∨ A=⊤ := by
  let P := omegaCore p K
  let : Fact (IsPGroup p P) := ⟨IsElementaryAbelian.isPGroup p P⟩
  let q := QuotientGroup.mk' (frattini P)
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk',frattini_eq_bot_of_isElementaryAbelian (R := P) (p := p)])
  intro A hA
  have hmap : ∀ g x, x∈A.map q → omegaFrattiniAction p K g x∈A.map q := by
    rintro g _ ⟨x,hx,rfl⟩
    refine ⟨MulAut.conjNormal g x,hA g x hx,?_⟩
    change QuotientGroup.mk' _ _ = quotientAut _ _ (QuotientGroup.mk' _ x)
    rw [quotientAut_apply_mk]
    rfl
  rcases hi (A.map q) hmap with hb | ht
  · exact Or.inl ((A.map_eq_bot_iff_of_injective hq).mp hb)
  · right
    apply map_injective (f := q) hq
    rw [map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact ht

/-- The literal noncentral-Fitting C-component has no faithful binary module of degree at most twelve. -/
theorem noncentral_fitting_binary_degree
    {κ : GroupClass.{u}} (hG : IsSQTK κ G) (hO : pCore 2 G=⊥)
    (hD : D.IsCComponent) (hn : ¬ fittingSubgroup D ≤ center D)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ) :
    15 ≤ Module.finrank (ZMod 2) V := by
  let : Group.IsPerfect D := hD.perfect
  obtain ⟨hs,hc⟩ := structure_of_noncentral hG hO hD hn
  have hw := (conclusion_with_omega_actions hG hO hD hn hs hc).2
  have hnontriv : Nat.card (fittingSubgroup D) ≠ 1 := by
    intro hh
    apply hn
    rw [card_eq_one.mp hh]
    exact bot_le
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hnontriv
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3,hshape⟩ := RadicalStructure.core_omega hs hd
  let P := omegaCore p D
  let e : omega (pCore p D) (p := p) 1 ≃* P :=
    (omega (pCore p D) (p := p) 1).equivMapOfInjective (pCore p D).subtype
      (pCore p D).subtype_injective
  have hP : XiOddQuotient p P := hshape.of_mulEquiv e
  rcases hP with ⟨he,hcard⟩ | ⟨he,hcard,_⟩
  · let : IsElementaryAbelian p P := he
    have hi := omega_irreducible_of_elementary (hw.2.2 p hd).2.2.1
    exact BinaryCoprimeDegree.perfect_irreducible_plane_degree ρ hf hp3 P hcard hi
  · let : IsExtraspecial p P := he
    have hb := BinaryCoprimeDegree.extraspecial_finrank_le (by omega : p≠2)
      (ρ.comp P.subtype) (hf.comp P.subtype_injective) hcard
    have hp4 : p ≠ 4 := by
      intro hh
      have hh' : Nat.Prime 4 := hh ▸ hp
      norm_num at hh'
    have hn := BinaryCoprimeDegree.twenty_le_prime_times_binary_order hp (by omega)
    omega

/-- The degree hypothesis in the C.5.12 pair-span consumer forces central Fitting subgroup. -/
theorem fitting_le_center_of_binary_degree_le_twelve
    {κ : GroupClass.{u}} (hG : IsSQTK κ G) (hO : pCore 2 G=⊥)
    (hD : D.IsCComponent)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 12) : fittingSubgroup D ≤ center D := by
  by_contra hn
  have hh := noncentral_fitting_binary_degree hG hO hD hn ρ hf
  omega
end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
