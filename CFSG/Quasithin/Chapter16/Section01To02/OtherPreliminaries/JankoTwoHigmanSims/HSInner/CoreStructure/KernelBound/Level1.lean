module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound.Generic

/-!
# HS pair-kernel search, residual level 1

The residual generators fix the listed base and preserve the displayed colors.
All 100 possible extensions of the previous prefixes are checked: any
extension passing the necessary pair-kernel screen is among these 2 prefixes.
Every finite identity is checked by Lean's kernel. The script in `source/`
produces witnesses only.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
printed p.274; ATLAS HSG1-p100B0 and the existing HS order certificate.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound
open Theory.GroupTheory
open Sporadic.LeechRelated.HS.OrderCertificate
open Sporadic.LeechRelated.HS.EvenLocalCandidates.LargeElementaryCentralizers (word_properties)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

def color1 (x : Fin 100) : Nat :=
  (41418392925577745862419088953836031128631004128342899271956265149142926051163498089240484839572999360774192165443225751715459671895288617203655387591727665591682913439639858561399814930559449919003490529591424 >>> (7 * x.val)) % 128

def base1 : List (Fin 100) := [0]

theorem residual1_spec {h : Perm} (hh : h ∈ H1) :
    (∀ b ∈ base1, h b = b) ∧ (∀ x, color1 (h x) = color1 x) := by
  exact word_properties gen1 inv1 inv1_spec color1 base1
    (by apply allFin; decide +kernel) hh

def forward1 (j : Fin 2) : Nat :=
  #[4100094770554042515533122004313285236735003534074830538881045787921142082201184208296423565880205964959118971074454247199955378650214568923506906026203450061729621922836307612900092799561144844784840892852764800, 440174060969935198421671855823452453303335729602066432417584480802556017913646647747547783742047793826221744588097957447323351697876889110465659625478116735906526764276638716706474827687206028967596796572044045][j.val]!

def backward1 (j : Fin 2) : Nat :=
  #[4100094770554042515533122004313285236735003534074830538881045787921142082201184208296423565880205964959118971074454247199955378650214568923506906026203450061729621922836307612900092799561144844784840892852764800, 2658970977075639020036466630553259026155462801759798486373833457171334168012196754931658353007743954491533597877806828911303830585852687677280511124705162568609116247444885329221198018722699080950431779829207381][j.val]!

def image1 (j : Fin 2) (x : Fin 100) : Fin 100 :=
  ⟨(forward1 j >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def preimage1 (j : Fin 2) (x : Fin 100) : Fin 100 :=
  ⟨(backward1 j >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

theorem inverse1 : ∀ j x, preimage1 j (image1 j x) = x := by
  apply allFin
  decide +kernel

def prefix1 (j : Fin 2) : Perm :=
  tablePerm (image1 j) (preimage1 j) (inverse1 j)
    (rightInverse_of_leftInverse_fin (inverse1 j))

def next1 (i : Fin 1) (j : Fin 100) : Fin 2 :=
  ⟨(33554432 >>> (1 * (100 * i.val + j.val))) % 2 % 2,
    Nat.mod_lt _ (by decide)⟩

theorem transition1 : ∀ (i : Fin 1) (j : Fin 100),
    screen color1 base1 (prefix0 i * rep0 j) = true →
    prefix0 i * rep0 j = prefix1 (next1 i j) := by
  have h : ∀ (i : Fin 1) (j : Fin 100),
      screen color1 base1 (prefix0 i * rep0 j) = true →
      ∀ x : Fin 100, (prefix0 i * rep0 j) x = prefix1 (next1 i j) x := by
    apply allFin
    decide +kernel
  intro i j hij
  exact Equiv.ext (h i j hij)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound
