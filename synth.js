
class XenCalcSynth extends Synth {

  constructor(waveform = "sine") {
    super();
    this.waveform = waveform;
  }

  /**
    * Play a note at the given frequency and with the given envelope and
    * velocity using the nth voice
    *
    * @param {integer} voice
    * @param {number} frequency
    * @param {Object} envelope
    * @param {number} [envelope.attackTime]
    * @param {number} [envelope.decayTime]
    * @param {number} [envelope.sustain]
    * @param {number} [envelope.releaseTime]
    * @param {number} [velocity=127]
    */
  playFreq(voiceID, frequency, envelope, velocity = 127) {
    this.init()

    // if this voice is already active, kill it
    if (!R.isNil(this.active_voices[voiceID])) {
      this.noteOff(voiceID);
    }

    const voice = new Voice(this.audioCtx, frequency, velocity);
    voice.bindDelay(this.delay);
    voice.bindSynth(this);
    if (envelope.attackTime  != undefined) { voice.attackTime  = envelope.attackTime ; }
    if (envelope.decayTime   != undefined) { voice.decayTime   = envelope.decayTime  ; }
    if (envelope.sustain     != undefined) { voice.sustain     = envelope.sustain    ; }
    if (envelope.releaseTime != undefined) { voice.releaseTime = envelope.releaseTime; }
    voice.start();
    this.active_voices[voiceID] = voice;

    console.log("Play note " + voiceID + " (" + frequency.toFixed(3) + " Hz) velocity " + velocity);
  }

  /**
    * Stop the frequency being played on the nth voice after a given number of
    * milliseconds
    *
    * @param {integer} voice
    * @param {number} milliseconds
    */
  stopFreqAfter(voiceID, milliseconds) {
    if (milliseconds == 0) {
      this.noteOff(voiceID);
    }
    else {
      setTimeout(() => this.noteOff(voiceID), milliseconds);
    }
  }
}

// A nice envelope for a sustained note, based on "organ"
const organ = { attackTime: 0.05, decayTime:   0.5
              , sustain:    0.7 , releaseTime: 0.5 };

// A function for generating "percussive" envelopes
function percussive(decayTime) {
  return { attackTime: 0.001, decayTime:   decayTime
         , sustain:    0.001, releaseTime: decayTime };
}
