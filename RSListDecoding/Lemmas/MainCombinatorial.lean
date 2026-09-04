import RSListDecoding.Lemmas.BoxWidthThreshold
import RSListDecoding.Lemmas.Explainer
import RSListDecoding.Lemmas.Interpolation
import RSListDecoding.Lemmas.Threshold
import RSListDecoding.Statements

/-!
# Combinatorial Reed--Solomon list-decoding theorem

This is the proof assembly for the scoped public statement.  For fixed
`0 < θ < 1`, one threshold on the derivative order handles the repaired
scaled-shell estimate and the floor loss in the interpolation box.  Shrinking
the existential `ε₀` enforces that threshold and the repaired fixed-constant
rank comparison.  The ambient explainer theorem, root count, and subcode
monotonicity then give the result for every `k ≤ K`.
-/

noncomputable section

namespace RSListDecoding

/-- The exact combinatorial statement selected in `FORMALIZATION_SCOPE.md`. -/
theorem combinatorialMainStatement_proved : CombinatorialMainStatement := by
  intro θ hθ hθ₁
  obtain ⟨dShell, hShell⟩ :=
    exists_scaledShellThreshold_for_roundedParameters hθ hθ₁
  obtain ⟨dBox, hBox⟩ :=
    exists_derivativeOrderThreshold_for_boxWidth hθ
  let D := max dShell dBox
  obtain ⟨ε₀, hε₀, hε₀one, hε₀paper, hε₀rank, hthreshold⟩ :=
    exists_epsilonZero_below_with_derivativeOrder_threshold
      hθ hθ₁ (repairedRankEpsilonBound_pos hθ hθ₁) D
  refine ⟨ε₀, hε₀, hε₀one, ?_, ?_⟩
  · simpa [manuscriptEpsilonBound] using hε₀paper
  · intro ε hε hεε₀ n hn hdK k q _hk hkK hq hnq hBq hMq alpha halpha
    have hε₁ : ε < 1 := hεε₀.trans_le hε₀one
    have hnpos : 0 < n := by omega
    have hD : D ≤ derivativeOrder ε θ := hthreshold ε hε hεε₀
    have hdShell : dShell ≤ derivativeOrder ε θ :=
      (Nat.le_max_left dShell dBox).trans hD
    have hdBox : dBox ≤ derivativeOrder ε θ :=
      (Nat.le_max_right dShell dBox).trans hD
    obtain ⟨_hbad, _hratio, hshell, hfactor⟩ :=
      hShell ε hε hdShell
    have hbox :
        2 ≤ θ * (multiplicity ε θ : ℝ) / 16 := by
      simpa only [multiplicity] using
        hBox (derivativeOrder ε θ) hdBox
    have hsmall : ε < repairedRankEpsilonBound θ :=
      hεε₀.trans_le hε₀rank
    apply scoped_list_bound_of_ambient_explainers
      hε hε₁ hθ hθ₁ hnpos hdK hkK hq hnq hBq hMq alpha
    intro y
    exact exists_scoped_ambient_explainer
      hε hε₁ hθ hθ₁ hnpos hdK hsmall hq hshell hfactor hbox
        alpha halpha y

end RSListDecoding
